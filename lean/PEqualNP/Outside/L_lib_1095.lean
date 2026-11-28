import Mathlib

namespace PEqualNP.Outside.L_lib_1095_aux

open scoped BigOperators

abbrev Word (k : Nat) := Fin k → ZMod 2

def dot {k : Nat} (a b : Word k) : ZMod 2 := ∑ r : Fin k, a r * b r

def sgn (x : ZMod 2) : Int := if x = 0 then 1 else -1

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

private lemma zmod2_ne_zero_iff (x : ZMod 2) : x ≠ 0 ↔ x = 1 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma sgn_add_one (a : ZMod 2) : sgn (a + 1) = -sgn a := by
  fin_cases a <;> decide

private lemma dot_add_left {k : Nat} (a b c : Word k) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right {k : Nat} (a b c : Word k) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

private lemma sum_sgn_involution {α : Type*} [Fintype α] (f : α → ZMod 2) (τ : α → α)
    (hinv : ∀ x, τ (τ x) = x) (hflip : ∀ x, f (τ x) = f x + 1) :
    (∑ x : α, sgn (f x)) = 0 := by
  have h1 : (∑ x : α, sgn (f x)) = ∑ x : α, sgn (f (τ x)) := by
    symm
    refine Fintype.sum_equiv (Equiv.ofBijective τ ⟨?_, ?_⟩) _ _ (fun _ => rfl)
    · intro x y h
      have := congrArg τ h
      simpa [hinv] using this
    · intro y
      exact ⟨τ y, hinv y⟩
  have h2 : (∑ x : α, sgn (f (τ x))) = -(∑ x : α, sgn (f x)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hflip x, sgn_add_one]
  omega

private lemma sum_sgn_dot {m : Nat} (w : Word m) :
    (∑ α : Word m, sgn (dot α w)) = if w = 0 then (2 : Int) ^ m else 0 := by
  by_cases hw : w = 0
  · subst hw
    simp [dot, sgn]
  · simp only [hw, if_false]
    have hex : ∃ r0 : Fin m, w r0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw (funext h)
    obtain ⟨r0, hr0⟩ := hex
    have hr01 : w r0 = 1 := (zmod2_ne_zero_iff (w r0)).mp hr0
    let τ : Word m → Word m := fun α => Function.update α r0 (α r0 + 1)
    apply sum_sgn_involution (fun α => dot α w) τ
    · intro α
      ext r
      by_cases hr : r = r0
      · subst hr
        simp [τ, add_assoc, zmod2_add_self]
      · simp [τ, hr]
    · intro α
      simp only [dot, τ]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r0),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ r0)]
      have hrest :
          (∑ r ∈ Finset.univ.erase r0, Function.update α r0 (α r0 + 1) r * w r) =
            ∑ r ∈ Finset.univ.erase r0, α r * w r := by
        refine Finset.sum_congr rfl (fun r hr => ?_)
        have hne : r ≠ r0 := (Finset.mem_erase.mp hr).1
        simp [hne]
      rw [hrest, Function.update_self, hr01]
      ring

private def localRuleDef (n : Nat) (D : Fin n → Finset (Fin n)) (T : Fin n → Word n → ZMod 2) : Prop :=
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y

private def observedDef (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
    (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) (r : Fin m) : ZMod 2 :=
  let x := fun i : Fin n => if h : i ∈ U then z ⟨i, h⟩ else b i
  ∑ i, (x i + T i x) * Q i r

private def uniformDef (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) : Prop :=
  ∀ T, localRuleDef n D T → ∀ b v,
    2 ^ m * Nat.card {z : U → ZMod 2 // observedDef n m Q U T b z = v} = 2 ^ U.card

private def readersDef (n : Nat) (D : Fin n → Finset (Fin n)) (j : Fin n) : Nat :=
  (Finset.univ.filter (fun i => j ∈ D i)).card

private def wiresDef (n : Nat) (D : Fin n → Finset (Fin n)) : Nat :=
  ∑ i, (D i).card

private def isPivot (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (α : Word m) (j : Fin n) : Prop :=
  dot α (Q j) = 1 ∧ ∀ i : Fin n, j ∈ D i → dot α (Q i) = 0

private lemma dot_observed (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
    (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) (α : Word m) :
    dot α (observedDef n m Q U T b z) =
      let x := fun i : Fin n => if h : i ∈ U then z ⟨i, h⟩ else b i
      ∑ i : Fin n, (x i + T i x) * dot α (Q i) := by
  simp only [dot, observedDef]
  calc
    ∑ r : Fin m, α r * ∑ i : Fin n, ((if h : i ∈ U then z ⟨i, h⟩ else b i) + T i (fun i => if h : i ∈ U then z ⟨i, h⟩ else b i)) * Q i r
      = ∑ r : Fin m, ∑ i : Fin n, α r * (((if h : i ∈ U then z ⟨i, h⟩ else b i) + T i (fun i => if h : i ∈ U then z ⟨i, h⟩ else b i)) * Q i r) := by
        refine Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)
    _ = ∑ i : Fin n, ∑ r : Fin m, α r * (((if h : i ∈ U then z ⟨i, h⟩ else b i) + T i (fun i => if h : i ∈ U then z ⟨i, h⟩ else b i)) * Q i r) := Finset.sum_comm
    _ = ∑ i : Fin n, ((if h : i ∈ U then z ⟨i, h⟩ else b i) + T i (fun i => if h : i ∈ U then z ⟨i, h⟩ else b i)) * ∑ r : Fin m, α r * Q i r := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => by ring)

private lemma uniform_of_pivots (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n))
    (hpiv : ∀ α : Word m, α ≠ 0 → ∃ j ∈ U, isPivot n m D Q α j) :
    uniformDef n m D Q U := by
  intro T hT b v
  have hcard_eq : Nat.card {z : U → ZMod 2 // observedDef n m Q U T b z = v} =
      (Finset.univ.filter (fun z : U → ZMod 2 => observedDef n m Q U T b z = v)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard_eq]
  have hint :
      ((2 ^ m * (Finset.univ.filter (fun z : U → ZMod 2 => observedDef n m Q U T b z = v)).card : Nat) : Int) =
        ((2 ^ U.card : Nat) : Int) := by
    have hsum1 :
        ((2 ^ m * (Finset.univ.filter (fun z : U → ZMod 2 => observedDef n m Q U T b z = v)).card : Nat) : Int) =
          ∑ z : U → ZMod 2, if observedDef n m Q U T b z + v = 0 then (2 : Int) ^ m else 0 := by
      have heq_iff : ∀ z : U → ZMod 2, observedDef n m Q U T b z + v = 0 ↔ observedDef n m Q U T b z = v := by
        intro z
        constructor
        · intro h
          funext r
          have hr := congrFun h r
          simp only [Pi.add_apply, Pi.zero_apply] at hr
          have := congrArg (fun t => t + v r) hr
          simpa [add_assoc, zmod2_add_self] using this
        · intro h
          rw [h]
          funext r
          exact zmod2_add_self (v r)
      simp only [heq_iff, Finset.sum_ite, Finset.sum_const, smul_eq_mul, Finset.sum_const_zero, add_zero]
      push_cast
      ring
    rw [hsum1]
    have hsum2 :
        (∑ z : U → ZMod 2, if observedDef n m Q U T b z + v = 0 then (2 : Int) ^ m else 0) =
          ∑ α : Word m, sgn (dot α v) * ∑ z : U → ZMod 2, sgn (dot α (observedDef n m Q U T b z)) := by
      calc
        (∑ z : U → ZMod 2, if observedDef n m Q U T b z + v = 0 then (2 : Int) ^ m else 0)
          = ∑ z : U → ZMod 2, ∑ α : Word m, sgn (dot α (observedDef n m Q U T b z + v)) := by
            refine Finset.sum_congr rfl (fun z _ => (sum_sgn_dot _).symm)
        _ = ∑ α : Word m, ∑ z : U → ZMod 2, sgn (dot α (observedDef n m Q U T b z + v)) := Finset.sum_comm
        _ = ∑ α : Word m, sgn (dot α v) * ∑ z : U → ZMod 2, sgn (dot α (observedDef n m Q U T b z)) := by
            refine Finset.sum_congr rfl (fun α _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            rw [dot_add_right, sgn_add, mul_comm]
    rw [hsum2, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Word m))]
    have hzero :
        sgn (dot (0 : Word m) v) * ∑ z : U → ZMod 2, sgn (dot (0 : Word m) (observedDef n m Q U T b z)) =
          ((2 ^ U.card : Nat) : Int) := by
      simp [dot, sgn]
    have hrest :
        (∑ α ∈ Finset.univ.erase (0 : Word m),
          sgn (dot α v) * ∑ z : U → ZMod 2, sgn (dot α (observedDef n m Q U T b z))) = 0 := by
      refine Finset.sum_eq_zero (fun α hα => ?_)
      have hαne : α ≠ 0 := (Finset.mem_erase.mp hα).1
      obtain ⟨j, hjU, hj1, hj0⟩ := hpiv α hαne
      have hinner : (∑ z : U → ZMod 2, sgn (dot α (observedDef n m Q U T b z))) = 0 := by
        let jU : U := ⟨j, hjU⟩
        let τ : (U → ZMod 2) → (U → ZMod 2) := fun z => Function.update z jU (z jU + 1)
        apply sum_sgn_involution (fun z => dot α (observedDef n m Q U T b z)) τ
        · intro z
          ext k
          by_cases hk : k = jU
          · subst hk
            simp [τ, add_assoc, zmod2_add_self]
          · simp [τ, hk]
        · intro z
          rw [dot_observed, dot_observed]
          dsimp only
          let x1 : Word n := fun i => if h : i ∈ U then z ⟨i, h⟩ else b i
          let x2 : Word n := fun i => if h : i ∈ U then τ z ⟨i, h⟩ else b i
          have hx_ne : ∀ i : Fin n, i ≠ j → x2 i = x1 i := by
            intro i hi
            by_cases hiU : i ∈ U
            · simp only [x1, x2, hiU, dite_true, τ]
              have hkne : (⟨i, hiU⟩ : U) ≠ jU := fun h => hi (congrArg Subtype.val h)
              simp [hkne]
            · simp [x1, x2, hiU]
          have hx_j : x2 j = x1 j + 1 := by
            simp [x1, x2, hjU, τ, jU]
          have hT_eq : ∀ i : Fin n, dot α (Q i) ≠ 0 → T i x2 = T i x1 := by
            intro i hdi
            apply hT i x2 x1
            intro k hk
            have hkj : k ≠ j := by
              intro h
              subst h
              exact hdi (hj0 i hk)
            exact hx_ne k hkj
          change (∑ i : Fin n, (x2 i + T i x2) * dot α (Q i)) =
            (∑ i : Fin n, (x1 i + T i x1) * dot α (Q i)) + 1
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
              ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have hsum_eq :
              (∑ i ∈ Finset.univ.erase j, (x2 i + T i x2) * dot α (Q i)) =
                ∑ i ∈ Finset.univ.erase j, (x1 i + T i x1) * dot α (Q i) := by
            refine Finset.sum_congr rfl (fun i hi => ?_)
            have hij : i ≠ j := (Finset.mem_erase.mp hi).1
            by_cases hdi : dot α (Q i) = 0
            · simp [hdi]
            · rw [hx_ne i hij, hT_eq i hdi]
          have hTj : T j x2 = T j x1 := hT_eq j (by rw [hj1]; decide)
          rw [hsum_eq, hx_j, hTj, hj1]
          ring
      rw [hinner, mul_zero]
    rw [hzero, hrest, add_zero]
  exact Int.ofNat.inj hint

private lemma pivots_of_uniform (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) (hunif : uniformDef n m D Q U) :
    ∀ α : Word m, α ≠ 0 → ∃ j ∈ U, isPivot n m D Q α j := by
  intro α hαne
  by_contra hnopiv
  push_neg at hnopiv
  have hcov : ∀ j ∈ U, dot α (Q j) = 1 → ∃ i : Fin n, j ∈ D i ∧ dot α (Q i) = 1 := by
    intro j hjU hj1
    have hnot := hnopiv j hjU
    unfold isPivot at hnot
    push_neg at hnot
    obtain ⟨i, hji, hdi⟩ := hnot hj1
    exact ⟨i, hji, (zmod2_ne_zero_iff _).mp hdi⟩
  let S : Finset (Fin n) := U.filter (fun j => dot α (Q j) = 1)
  have hcov' : ∀ j : Fin n, j ∈ S → ∃ i : Fin n, j ∈ D i ∧ dot α (Q i) = 1 := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact hcov j hj'.1 hj'.2
  classical
  let pick : Fin n → Fin n := fun j => if h : j ∈ S then Classical.choose (hcov' j h) else j
  have hpick_mem : ∀ j (hj : j ∈ S), j ∈ D (pick j) ∧ dot α (Q (pick j)) = 1 := by
    intro j hj
    simpa [pick, hj] using Classical.choose_spec (hcov' j hj)
  let T : Fin n → Word n → ZMod 2 := fun i x =>
    ∑ j ∈ S.filter (fun j => pick j = i), x j
  have hT : localRuleDef n D T := by
    intro i x y hxy
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
    have hpi : pick j = i := (Finset.mem_filter.mp hj).2
    apply hxy j
    rw [← hpi]
    exact (hpick_mem j hjS).1
  have hdot_zero : ∀ z : U → ZMod 2, dot α (observedDef n m Q U T 0 z) = 0 := by
    intro z
    rw [dot_observed]
    dsimp only
    let x : Word n := fun i => if h : i ∈ U then z ⟨i, h⟩ else 0
    change (∑ i : Fin n, (x i + T i x) * dot α (Q i)) = 0
    have hsplit :
        (∑ i : Fin n, (x i + T i x) * dot α (Q i)) =
          (∑ i : Fin n, x i * dot α (Q i)) + ∑ i : Fin n, T i x * dot α (Q i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit]
    have h1 : (∑ i : Fin n, x i * dot α (Q i)) = ∑ j ∈ S, x j := by
      have : (∑ i : Fin n, x i * dot α (Q i)) = ∑ i ∈ S, x i * dot α (Q i) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hiS => ?_)
        by_cases hiU : i ∈ U
        · have hne1 : dot α (Q i) ≠ 1 := fun h1 => hiS (Finset.mem_filter.mpr ⟨hiU, h1⟩)
          have h0 : dot α (Q i) = 0 := by
            rcases zmod2_cases (dot α (Q i)) with h | h
            · exact h
            · exact False.elim (hne1 h)
          simp [h0]
        · simp [x, hiU]
      rw [this]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have h1' : dot α (Q j) = 1 := (Finset.mem_filter.mp hj).2
      simp [h1']
    have h2 : (∑ i : Fin n, T i x * dot α (Q i)) = ∑ j ∈ S, x j := by
      have hTmul : ∀ i : Fin n, T i x * dot α (Q i) = ∑ j ∈ S.filter (fun j => pick j = i), x j := by
        intro i
        by_cases hi : ∃ j ∈ S, pick j = i
        · obtain ⟨j0, hj0S, hp0⟩ := hi
          have hdi : dot α (Q i) = 1 := by
            rw [← hp0]
            exact (hpick_mem j0 hj0S).2
          simp [T, hdi]
        · have hemp : S.filter (fun j => pick j = i) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro j hj hp
            exact hi ⟨j, hj, hp⟩
          simp [T, hemp]
      simp_rw [hTmul]
      rw [← Finset.sum_biUnion]
      · congr 1
        ext j
        simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
        exact ⟨fun ⟨_, hjS, _⟩ => hjS, fun hjS => ⟨pick j, hjS, rfl⟩⟩
      · intro i1 _ i2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        exact hne ((Finset.mem_filter.mp hj1).2.symm.trans (Finset.mem_filter.mp hj2).2)
    rw [h1, h2]
    exact zmod2_add_self _
  have hex_r : ∃ r0 : Fin m, α r0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hαne (funext h)
  obtain ⟨r0, hr0⟩ := hex_r
  let v : Word m := fun r => if r = r0 then 1 else 0
  have hdv : dot α v = 1 := by
    simp only [dot, v]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r0)]
    have hrest : (∑ r ∈ Finset.univ.erase r0, α r * (if r = r0 then (1 : ZMod 2) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun r hr => ?_)
      simp [(Finset.mem_erase.mp hr).1]
    rw [hrest, add_zero, if_pos rfl, mul_one]
    exact (zmod2_ne_zero_iff _).mp hr0
  have hcard0 : Nat.card {z : U → ZMod 2 // observedDef n m Q U T 0 z = v} = 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨z, hz⟩ => ?_⟩
    have h0 := hdot_zero z
    rw [hz, hdv] at h0
    exact absurd h0 (by decide)
  have hu := hunif T hT 0 v
  rw [hcard0, mul_zero] at hu
  have hpos : 0 < 2 ^ U.card := by positivity
  omega

private lemma uniform_iff_pivots (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) :
    uniformDef n m D Q U ↔ ∀ α : Word m, α ≠ 0 → ∃ j ∈ U, isPivot n m D Q α j :=
  ⟨pivots_of_uniform n m D Q U, uniform_of_pivots n m D Q U⟩

private lemma wires_eq_sum_readers (n : Nat) (D : Fin n → Finset (Fin n)) :
    wiresDef n D = ∑ j : Fin n, readersDef n D j := by
  simp only [wiresDef, readersDef]
  have h1 : ∀ i : Fin n, (D i).card = ∑ j : Fin n, if j ∈ D i then 1 else 0 := by
    intro i
    simp [Finset.sum_boole]
  have h2 : ∀ j : Fin n, (Finset.univ.filter (fun i => j ∈ D i)).card = ∑ i : Fin n, if j ∈ D i then 1 else 0 := by
    intro j
    simp [Finset.sum_boole]
  simp_rw [h1, h2]
  exact Finset.sum_comm

-- PART 2: LOWER BOUND

private lemma lower_bound (m : Nat) (hm : 1 ≤ m) (n : Nat) (D : Fin n → Finset (Fin n))
    (Q : Fin n → Word m) (W : Finset (Fin n))
    (hWcard : W.card = 2 ^ m - 1)
    (hunif : uniformDef n m D Q Finset.univ)
    (hcrit : ∀ j ∈ W, ¬ uniformDef n m D Q (Finset.univ.erase j)) :
    2 ^ m - 1 ≤ n ∧ (∀ j ∈ W, m - 1 ≤ readersDef n D j) ∧ (2 ^ m - 1) * (m - 1) ≤ wiresDef n D := by
  have hNle : 2 ^ m - 1 ≤ n := by
    rw [← hWcard]
    simpa using Finset.card_le_univ W
  have hpiv_all := (uniform_iff_pivots n m D Q Finset.univ).mp hunif
  have hex_alpha : ∀ j ∈ W, ∃ α : Word m, α ≠ 0 ∧ isPivot n m D Q α j ∧
      ∀ k : Fin n, isPivot n m D Q α k → k = j := by
    intro j hjW
    have hnot := hcrit j hjW
    rw [uniform_iff_pivots] at hnot
    push_neg at hnot
    obtain ⟨α, hαne, hno⟩ := hnot
    obtain ⟨k, _, hk⟩ := hpiv_all α hαne
    have hkj : k = j := by
      by_contra hne
      exact hno k (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k⟩) hk
    subst hkj
    refine ⟨α, hαne, hk, ?_⟩
    intro k' hk'
    by_contra hne
    exact hno k' (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k'⟩) hk'
  classical
  let αOf : Fin n → Word m := fun j => if h : j ∈ W then Classical.choose (hex_alpha j h) else 0
  have hαOf_spec : ∀ j (hj : j ∈ W), αOf j ≠ 0 ∧ isPivot n m D Q (αOf j) j ∧
      ∀ k : Fin n, isPivot n m D Q (αOf j) k → k = j := by
    intro j hj
    simpa [αOf, hj] using Classical.choose_spec (hex_alpha j hj)
  have hαOf_inj : Set.InjOn αOf (W : Set (Fin n)) := by
    intro j1 hj1 j2 hj2 heq
    have h2 := (hαOf_spec j2 hj2).2.1
    rw [← heq] at h2
    exact ((hαOf_spec j1 hj1).2.2 j2 h2).symm
  have hnz_card : (Finset.univ.erase (0 : Word m)).card = 2 ^ m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have himg_eq : W.image αOf = Finset.univ.erase (0 : Word m) := by
    apply Finset.eq_of_subset_of_card_le
    · intro α hα
      obtain ⟨j, hjW, rfl⟩ := Finset.mem_image.mp hα
      exact Finset.mem_erase.mpr ⟨(hαOf_spec j hjW).1, Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injOn hαOf_inj, hWcard, hnz_card]
  have huniq_pivot : ∀ j ∈ W, ∀ β : Word m, isPivot n m D Q β j → β = αOf j := by
    intro j hjW β hβpiv
    have hβne : β ≠ 0 := by
      intro h0
      have h1 := hβpiv.1
      simp [h0, dot] at h1
    have hmem : β ∈ W.image αOf := by
      rw [himg_eq]
      exact Finset.mem_erase.mpr ⟨hβne, Finset.mem_univ _⟩
    obtain ⟨k, hkW, rfl⟩ := Finset.mem_image.mp hmem
    have hjk : j = k := (hαOf_spec k hkW).2.2 j hβpiv
    subst hjk
    rfl
  have hreaders : ∀ j ∈ W, m - 1 ≤ readersDef n D j := by
    intro j hjW
    let Rj : Finset (Fin n) := Finset.univ.filter (fun i => j ∈ D i)
    let Φ : Word m → (Rj → ZMod 2) := fun β i => dot β (Q i.val)
    have hker : ∀ γ : Word m, Φ γ = 0 → γ = 0 ∨ γ = αOf j := by
      intro γ hΦγ
      have hγR : ∀ i : Fin n, j ∈ D i → dot γ (Q i) = 0 := by
        intro i hi
        have him : i ∈ Rj := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        exact congrFun hΦγ ⟨i, him⟩
      rcases zmod2_cases (dot γ (Q j)) with h0 | h1
      · left
        have hβpiv : isPivot n m D Q (αOf j + γ) j := by
          refine ⟨?_, ?_⟩
          · rw [dot_add_left, (hαOf_spec j hjW).2.1.1, h0, add_zero]
          · intro i hi
            rw [dot_add_left, (hαOf_spec j hjW).2.1.2 i hi, hγR i hi, add_zero]
        have heq := huniq_pivot j hjW (αOf j + γ) hβpiv
        funext r
        have hr := congrFun heq r
        simp only [Pi.add_apply] at hr
        have := congrArg (fun t => αOf j r + t) hr
        simpa [← add_assoc, zmod2_add_self] using this
      · right
        exact huniq_pivot j hjW γ ⟨h1, hγR⟩
    have hfiber : ∀ y : Rj → ZMod 2,
        (Finset.univ.filter (fun β : Word m => Φ β = y)).card ≤ 2 := by
      intro y
      by_cases hex : ∃ β0 : Word m, Φ β0 = y
      · obtain ⟨β0, rfl⟩ := hex
        have hsub : Finset.univ.filter (fun β : Word m => Φ β = Φ β0) ⊆ {β0, β0 + αOf j} := by
          intro β hβ
          have hΦeq : Φ β = Φ β0 := (Finset.mem_filter.mp hβ).2
          have hΦdiff : Φ (β + β0) = 0 := by
            funext i
            change dot (β + β0) (Q i.val) = 0
            rw [dot_add_left]
            have hi := congrFun hΦeq i
            change dot β (Q i.val) = dot β0 (Q i.val) at hi
            rw [hi, zmod2_add_self]
          rcases hker (β + β0) hΦdiff with h0 | hα
          · have hβeq : β = β0 := by
              funext r
              have hr := congrFun h0 r
              simp only [Pi.add_apply, Pi.zero_apply] at hr
              have := congrArg (fun t => t + β0 r) hr
              simpa [add_assoc, zmod2_add_self] using this
            rw [hβeq]
            exact Finset.mem_insert_self _ _
          · have hβeq : β = β0 + αOf j := by
              funext r
              have hr := congrFun hα r
              simp only [Pi.add_apply] at hr
              have := congrArg (fun t => t + β0 r) hr
              have h1 : β r = αOf j r + β0 r := by simpa [add_assoc, zmod2_add_self] using this
              simp only [Pi.add_apply]
              rw [h1, add_comm]
            rw [hβeq]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        calc
          (Finset.univ.filter (fun β : Word m => Φ β = Φ β0)).card
            ≤ ({β0, β0 + αOf j} : Finset (Word m)).card := Finset.card_le_card hsub
          _ ≤ 2 := Finset.card_le_two
      · push_neg at hex
        have hemp : Finset.univ.filter (fun β : Word m => Φ β = y) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro β _
          exact hex β
        rw [hemp]
        simp
    have hpow : 2 ^ m ≤ 2 ^ (Rj.card + 1) := by
      have hpart : (Finset.univ : Finset (Word m)).card =
          ∑ y : Rj → ZMod 2, (Finset.univ.filter (fun β : Word m => Φ β = y)).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext β
          simp
        · intro y1 _ y2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro β h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hle : (Finset.univ : Finset (Word m)).card ≤ ∑ _y : Rj → ZMod 2, 2 := by
        rw [hpart]
        exact Finset.sum_le_sum (fun y _ => hfiber y)
      simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_coe, ZMod.card,
        Finset.prod_const, Finset.sum_const, smul_eq_mul] at hle
      simpa [pow_succ, mul_comm] using hle
    have hle' : m ≤ Rj.card + 1 := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
    change m - 1 ≤ Rj.card
    omega
  have hwires : (2 ^ m - 1) * (m - 1) ≤ wiresDef n D := by
    rw [wires_eq_sum_readers]
    calc
      (2 ^ m - 1) * (m - 1) = W.card * (m - 1) := by rw [hWcard]
      _ = ∑ _j ∈ W, (m - 1) := by simp
      _ ≤ ∑ j ∈ W, readersDef n D j := Finset.sum_le_sum hreaders
      _ ≤ ∑ j : Fin n, readersDef n D j := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  exact ⟨hNle, hreaders, hwires⟩

-- PART 1: UPPER BOUND CONSTRUCTION

-- Binary encoding between Fin (2^m - 1) and nonzero Word m
private def toMask (m : Nat) (i : Fin (2 ^ m - 1)) : Word m :=
  fun r => if (i.val + 1).testBit r.val then 1 else 0

private def fromMask (m : Nat) (α : Word m) : Nat :=
  ∑ r : Fin m, if α r = 1 then 2 ^ r.val else 0

private lemma fromMask_lt (m : Nat) (α : Word m) : fromMask m α < 2 ^ m := by
  induction m with
  | zero =>
    simp [fromMask]
  | succ m ih =>
    unfold fromMask
    rw [Fin.sum_univ_castSucc]
    have hprev : (∑ r : Fin m, if α r.castSucc = 1 then 2 ^ r.castSucc.val else 0) < 2 ^ m := by
      simpa [fromMask] using ih (fun r => α r.castSucc)
    have hlast : (if α (Fin.last m) = 1 then 2 ^ (Fin.last m).val else 0) ≤ 2 ^ m := by
      split_ifs <;> simp
    have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega

private lemma testBit_fromMask (m : Nat) (α : Word m) (r : Fin m) :
    (fromMask m α).testBit r.val = decide (α r = 1) := by
  induction m with
  | zero => exact Fin.elim0 r
  | succ m ih =>
    have hdecomp : fromMask (m + 1) α =
        (if α 0 = 1 then 1 else 0) + 2 * fromMask m (fun k => α k.succ) := by
      unfold fromMask
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ', Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> ring
    rw [hdecomp]
    cases r using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.testBit_zero]
      split_ifs with h
      · simp [h]
      · simp [h]
    | succ k =>
      simp only [Fin.val_succ]
      have hdiv : ((if α 0 = 1 then 1 else 0) + 2 * fromMask m (fun j => α j.succ)) / 2 =
          fromMask m (fun j => α j.succ) := by
        split_ifs <;> omega
      rw [Nat.testBit_succ, hdiv]
      exact ih (fun j => α j.succ) k

private lemma fromMask_pos_of_ne_zero (m : Nat) (α : Word m) (hα : α ≠ 0) :
    0 < fromMask m α := by
  have hex : ∃ r : Fin m, α r ≠ 0 := by
    by_contra h
    push_neg at h
    exact hα (funext h)
  obtain ⟨r, hr⟩ := hex
  have hr1 : α r = 1 := (zmod2_ne_zero_iff _).mp hr
  unfold fromMask
  have hle : (if α r = 1 then 2 ^ r.val else 0) ≤ ∑ k : Fin m, if α k = 1 then 2 ^ k.val else 0 :=
    Finset.single_le_sum (f := fun k : Fin m => if α k = 1 then 2 ^ k.val else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  rw [if_pos hr1] at hle
  have hpos : 0 < 2 ^ r.val := by positivity
  omega

private lemma fromMask_toMask_nat (m : Nat) (x : Nat) (hx : x < 2 ^ m) :
    (∑ r : Fin m, if x.testBit r.val then 2 ^ r.val else 0) = x := by
  induction m generalizing x with
  | zero =>
    simp at hx
    simp [hx]
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ']
    have hdiv : x / 2 < 2 ^ m := by
      have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    have htail :
        (∑ k : Fin m, if x.testBit (k.val + 1) then 2 * 2 ^ k.val else 0) =
          2 * ∑ k : Fin m, if (x / 2).testBit k.val then 2 ^ k.val else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Nat.testBit_succ]
      split_ifs <;> ring
    rw [htail, ih (x / 2) hdiv, Nat.testBit_zero]
    by_cases hmod : x % 2 = 1
    · simp [hmod]
      omega
    · have hmod0 : x % 2 = 0 := by omega
      simp [hmod0]
      omega

private lemma fromMask_toMask (m : Nat) (i : Fin (2 ^ m - 1)) :
    fromMask m (toMask m i) = i.val + 1 := by
  have hx : i.val + 1 < 2 ^ m := by
    have h1 := i.isLt
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
    omega
  have h := fromMask_toMask_nat m (i.val + 1) hx
  unfold fromMask toMask
  convert h using 2 with r
  by_cases hb : (i.val + 1).testBit r.val = true
  · simp [hb]
  · simp [hb]

private lemma toMask_ne_zero (m : Nat) (i : Fin (2 ^ m - 1)) : toMask m i ≠ 0 := by
  intro h0
  have h := fromMask_toMask m i
  rw [h0] at h
  simp [fromMask] at h

private lemma toMask_inj (m : Nat) : Function.Injective (toMask m) := by
  intro i j hij
  have h := congrArg (fromMask m) hij
  rw [fromMask_toMask, fromMask_toMask] at h
  exact Fin.ext (by omega)

private def idxOf (m : Nat) (α : Word m) (hα : α ≠ 0) : Fin (2 ^ m - 1) :=
  ⟨fromMask m α - 1, by
    have h1 := fromMask_pos_of_ne_zero m α hα
    have h2 := fromMask_lt m α
    omega⟩

private lemma toMask_idxOf (m : Nat) (α : Word m) (hα : α ≠ 0) :
    toMask m (idxOf m α hα) = α := by
  funext r
  have h1 := fromMask_pos_of_ne_zero m α hα
  have hv : (idxOf m α hα).val + 1 = fromMask m α := by
    simp only [idxOf]
    omega
  simp only [toMask, hv, testBit_fromMask]
  rcases zmod2_cases (α r) with h0 | h1'
  · simp [h0]
  · simp [h1']

private lemma idxOf_toMask (m : Nat) (i : Fin (2 ^ m - 1)) :
    idxOf m (toMask m i) (toMask_ne_zero m i) = i := by
  apply toMask_inj m
  exact toMask_idxOf m (toMask m i) (toMask_ne_zero m i)

-- Generic constructor from a family (Q, R) where R j is a reader set of size m-1 spanning (toMask j)^perp
private lemma upper_from_QR (m : Nat) (Q : Fin (2 ^ m - 1) → Word m)
    (R : Fin (2 ^ m - 1) → Finset (Fin (2 ^ m - 1)))
    (hwt : ∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2)
    (hRcard : ∀ j, (R j).card = m - 1)
    (hdiag : ∀ j, dot (toMask m j) (Q j) = 1)
    (horth : ∀ j, ∀ i ∈ R j, dot (toMask m j) (Q i) = 0)
    (hspan : ∀ j (β : Word m), (∀ i ∈ R j, dot β (Q i) = 0) → β = 0 ∨ β = toMask m j) :
    ∃ (D : Fin (2 ^ m - 1) → Finset (Fin (2 ^ m - 1))) (Q' : Fin (2 ^ m - 1) → Word m),
      (∀ i, i ∉ D i) ∧
      (∀ i, (Finset.univ.filter (fun r => Q' i r ≠ 0)).card ≤ 2) ∧
      (∀ j, readersDef (2 ^ m - 1) D j = m - 1) ∧
      wiresDef (2 ^ m - 1) D = (2 ^ m - 1) * (m - 1) ∧
      (∀ U, uniformDef (2 ^ m - 1) m D Q' U ↔ U = Finset.univ) := by
  let N := 2 ^ m - 1
  let D : Fin N → Finset (Fin N) := fun i => Finset.univ.filter (fun j => i ∈ R j)
  refine ⟨D, Q, ?_, hwt, ?_, ?_, ?_⟩
  · intro i hi
    have hiR : i ∈ R i := (Finset.mem_filter.mp hi).2
    have h0 := horth i i hiR
    have h1 := hdiag i
    rw [h0] at h1
    exact absurd h1 (by decide)
  · intro j
    have heq : Finset.univ.filter (fun i : Fin N => j ∈ D i) = R j := by
      ext i
      simp [D]
    change (Finset.univ.filter (fun i : Fin N => j ∈ D i)).card = m - 1
    rw [heq, hRcard j]
  · rw [wires_eq_sum_readers]
    have hread : ∀ j : Fin N, readersDef N D j = m - 1 := by
      intro j
      have heq : Finset.univ.filter (fun i : Fin N => j ∈ D i) = R j := by
        ext i
        simp [D]
      change (Finset.univ.filter (fun i : Fin N => j ∈ D i)).card = m - 1
      rw [heq, hRcard j]
    simp [hread, N]
  · intro U
    rw [uniform_iff_pivots]
    constructor
    · intro hpiv
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      obtain ⟨k, hkU, hk1, hk0⟩ := hpiv (toMask m j) (toMask_ne_zero m j)
      have hperp : ∀ i ∈ R k, dot (toMask m j) (Q i) = 0 := by
        intro i hiRk
        exact hk0 i (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hiRk⟩)
      rcases hspan k (toMask m j) hperp with h0 | heq
      · exact False.elim (toMask_ne_zero m j h0)
      · have hjk : j = k := toMask_inj m heq
        rwa [hjk]
    · intro hU
      subst hU
      intro α hαne
      let j := idxOf m α hαne
      refine ⟨j, Finset.mem_univ j, ?_, ?_⟩
      · have := hdiag j
        rwa [toMask_idxOf] at this
      · intro i hi
        have hiRj : i ∈ R j := (Finset.mem_filter.mp hi).2
        have := horth j i hiRj
        rwa [toMask_idxOf] at this

-- m = 1
private lemma upper_m1 :
    ∃ (D : Fin (2 ^ 1 - 1) → Finset (Fin (2 ^ 1 - 1))) (Q : Fin (2 ^ 1 - 1) → Word 1),
      (∀ i, i ∉ D i) ∧
      (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
      (∀ j, readersDef (2 ^ 1 - 1) D j = 1 - 1) ∧
      wiresDef (2 ^ 1 - 1) D = (2 ^ 1 - 1) * (1 - 1) ∧
      (∀ U, uniformDef (2 ^ 1 - 1) 1 D Q U ↔ U = Finset.univ) := by
  apply upper_from_QR 1 (fun _ _ => 1) (fun _ => ∅)
  · intro i; decide
  · intro j; simp
  · intro j; fin_cases j; decide
  · intro j i hi; simp at hi
  · intro j β _
    fin_cases j
    by_cases h : β 0 = 0
    · left; funext r; fin_cases r; exact h
    · right
      have h1 : β 0 = 1 := (zmod2_ne_zero_iff _).mp h
      funext r; fin_cases r; dsimp; rw [h1]; decide

-- m = 2
private def Q2 : Fin 3 → Word 2
  | ⟨0, _⟩ => ![1, 1]
  | ⟨1, _⟩ => ![0, 1]
  | ⟨2, _⟩ => ![1, 0]

private def R2 : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => {⟨1, by omega⟩}
  | ⟨1, _⟩ => {⟨2, by omega⟩}
  | ⟨2, _⟩ => {⟨0, by omega⟩}

private lemma upper_m2 :
    ∃ (D : Fin (2 ^ 2 - 1) → Finset (Fin (2 ^ 2 - 1))) (Q : Fin (2 ^ 2 - 1) → Word 2),
      (∀ i, i ∉ D i) ∧
      (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
      (∀ j, readersDef (2 ^ 2 - 1) D j = 2 - 1) ∧
      wiresDef (2 ^ 2 - 1) D = (2 ^ 2 - 1) * (2 - 1) ∧
      (∀ U, uniformDef (2 ^ 2 - 1) 2 D Q U ↔ U = Finset.univ) := by
  apply upper_from_QR 2 Q2 R2
  · intro i; fin_cases i <;> decide
  · intro j; fin_cases j <;> decide
  · intro j; fin_cases j <;> decide
  · intro j i hi; fin_cases j <;> fin_cases i <;> simp [R2] at hi <;> decide
  · intro j β hβ
    have h0 : β 0 = 0 ∨ β 0 = 1 := zmod2_cases (β 0)
    have h1 : β 1 = 0 ∨ β 1 = 1 := zmod2_cases (β 1)
    fin_cases j
    · have hq := hβ ⟨1, by omega⟩ (by simp [R2])
      simp only [dot, Q2, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_zero, zero_add, mul_one] at hq
      rcases h0 with hb0 | hb0
      · left; funext r; fin_cases r <;> dsimp <;> assumption
      · right; funext r; fin_cases r <;> dsimp
        · rw [hb0]; decide
        · rw [hq]; decide
    · have hq := hβ ⟨2, by omega⟩ (by simp [R2])
      simp only [dot, Q2, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_zero, add_zero, mul_one] at hq
      rcases h1 with hb1 | hb1
      · left; funext r; fin_cases r <;> dsimp <;> assumption
      · right; funext r; fin_cases r <;> dsimp
        · rw [hq]; decide
        · rw [hb1]; decide
    · have hq := hβ ⟨0, by omega⟩ (by simp [R2])
      simp only [dot, Q2, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_one] at hq
      rcases h0 with hb0 | hb0 <;> rcases h1 with hb1 | hb1
      · left; funext r; fin_cases r <;> dsimp <;> assumption
      · simp [hb0, hb1] at hq
      · simp [hb0, hb1] at hq
      · right; funext r; fin_cases r <;> dsimp
        · rw [hb0]; decide
        · rw [hb1]; decide

-- m >= 3
private def eVec {m : Nat} (r : Fin m) : Word m := fun t => if t = r then 1 else 0

private def pVec {m : Nat} (a b : Fin m) : Word m :=
  fun t => (if t = a then 1 else 0) + (if t = b then 1 else 0)

private lemma eVec_ne_zero {m : Nat} (r : Fin m) : eVec r ≠ 0 := by
  intro h
  have := congrFun h r
  simp [eVec] at this

private lemma pVec_ne_zero {m : Nat} (a b : Fin m) (hab : a ≠ b) : pVec a b ≠ 0 := by
  intro h
  have := congrFun h a
  simp [pVec, hab] at this

private lemma dot_eVec {m : Nat} (β : Word m) (r : Fin m) : dot β (eVec r) = β r := by
  simp only [dot, eVec]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  have hrest : (∑ t ∈ Finset.univ.erase r, β t * (if t = r then (1 : ZMod 2) else 0)) = 0 := by
    refine Finset.sum_eq_zero (fun t ht => ?_)
    simp [(Finset.mem_erase.mp ht).1]
  rw [hrest, add_zero, if_pos rfl, mul_one]

private lemma dot_pVec {m : Nat} (β : Word m) (a b : Fin m) :
    dot β (pVec a b) = β a + β b := by
  have hp : pVec a b = eVec a + eVec b := rfl
  rw [hp, dot_add_right, dot_eVec, dot_eVec]

private lemma supp_eVec {m : Nat} (r : Fin m) :
    Finset.univ.filter (fun t : Fin m => eVec r t ≠ 0) = {r} := by
  ext t
  simp [eVec]

private lemma supp_pVec {m : Nat} (a b : Fin m) (hab : a ≠ b) :
    Finset.univ.filter (fun t : Fin m => pVec a b t ≠ 0) = {a, b} := by
  ext t
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and, pVec]
  by_cases hta : t = a
  · subst hta
    simp [hab]
  · by_cases htb : t = b
    · subst htb
      simp [hta]
    · simp [hta, htb]

private def nextPair {m : Nat} (hm : 3 ≤ m) (a b : Fin m) : Fin m × Fin m :=
  if h3 : 3 ≤ b.val then
    (⟨(a.val + 1) % b.val, lt_trans (Nat.mod_lt _ (by omega)) b.isLt⟩, b)
  else if a.val = 0 ∧ b.val = 1 then
    (⟨1, by omega⟩, ⟨2, by omega⟩)
  else if a.val = 1 ∧ b.val = 2 then
    (⟨0, by omega⟩, ⟨2, by omega⟩)
  else
    (⟨0, by omega⟩, ⟨1, by omega⟩)

private def prevPair {m : Nat} (hm : 3 ≤ m) (a b : Fin m) : Fin m × Fin m :=
  if h3 : 3 ≤ b.val then
    (⟨(a.val + b.val - 1) % b.val, lt_trans (Nat.mod_lt _ (by omega)) b.isLt⟩, b)
  else if a.val = 1 ∧ b.val = 2 then
    (⟨0, by omega⟩, ⟨1, by omega⟩)
  else if a.val = 0 ∧ b.val = 2 then
    (⟨1, by omega⟩, ⟨2, by omega⟩)
  else
    (⟨0, by omega⟩, ⟨2, by omega⟩)

private lemma nextPair_lt {m : Nat} (hm : 3 ≤ m) (a b : Fin m) (hab : a < b) :
    (nextPair hm a b).1 < (nextPair hm a b).2 := by
  unfold nextPair
  split_ifs with h3 h1 h2
  · exact Nat.mod_lt _ (by omega)
  · change (1 : Nat) < 2; omega
  · change (0 : Nat) < 2; omega
  · change (0 : Nat) < 1; omega

private lemma prevPair_lt {m : Nat} (hm : 3 ≤ m) (a b : Fin m) (hab : a < b) :
    (prevPair hm a b).1 < (prevPair hm a b).2 := by
  unfold prevPair
  split_ifs with h3 h1 h2
  · exact Nat.mod_lt _ (by omega)
  · change (0 : Nat) < 1; omega
  · change (1 : Nat) < 2; omega
  · change (0 : Nat) < 2; omega

private lemma nextPair_prevPair {m : Nat} (hm : 3 ≤ m) (a b : Fin m) (hab : a < b) :
    nextPair hm (prevPair hm a b).1 (prevPair hm a b).2 = (a, b) := by
  unfold prevPair
  split_ifs with h3 h1 h2
  · unfold nextPair
    rw [dif_pos h3]
    ext
    · change ((a.val + b.val - 1) % b.val + 1) % b.val = a.val
      have ha : a.val < b.val := hab
      have hmod : ((a.val + b.val - 1) % b.val + 1) % b.val = (a.val + b.val - 1 + 1) % b.val := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [hmod]
      have hsub : a.val + b.val - 1 + 1 = a.val + b.val := by omega
      rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
    · rfl
  · unfold nextPair
    have hnot : ¬ (3 ≤ (1 : Nat)) := by omega
    simp only [hnot, dite_false, true_and, and_self, ite_true]
    ext <;> simp [h1.1, h1.2]
  · unfold nextPair
    have hnot : ¬ (3 ≤ (2 : Nat)) := by omega
    have hne : ¬ ((1 : Nat) = 0 ∧ (2 : Nat) = 1) := by omega
    simp only [hnot, dite_false, hne, ite_false, and_self, ite_true]
    ext <;> simp [h2.1, h2.2]
  · have ha : a.val < b.val := hab
    have h01 : a.val = 0 ∧ b.val = 1 := by omega
    unfold nextPair
    have hnot : ¬ (3 ≤ (2 : Nat)) := by omega
    have hne1 : ¬ ((0 : Nat) = 0 ∧ (2 : Nat) = 1) := by omega
    have hne2 : ¬ ((0 : Nat) = 1 ∧ (2 : Nat) = 2) := by omega
    simp only [hnot, dite_false, hne1, hne2, ite_false]
    ext <;> simp [h01.1, h01.2]

private lemma nextPair_dot_one {m : Nat} (hm : 3 ≤ m) (a b : Fin m) (hab : a < b) :
    dot (pVec a b) (pVec (nextPair hm a b).1 (nextPair hm a b).2) = 1 := by
  rw [dot_pVec]
  unfold nextPair
  have ha : a.val < b.val := hab
  have hab_ne : a ≠ b := ne_of_lt hab
  split_ifs with h3 h1 h2
  · dsimp only
    let a' : Fin m := ⟨(a.val + 1) % b.val, lt_trans (Nat.mod_lt _ (by omega)) b.isLt⟩
    have ha'_ne_a : a' ≠ a := by
      intro h
      have hv : (a.val + 1) % b.val = a.val := congrArg Fin.val h
      by_cases htop : a.val + 1 < b.val
      · rw [Nat.mod_eq_of_lt htop] at hv; omega
      · have heq : a.val + 1 = b.val := by omega
        rw [heq, Nat.mod_self] at hv; omega
    have ha'_ne_b : a' ≠ b := by
      intro h
      have hv : (a.val + 1) % b.val = b.val := congrArg Fin.val h
      have hlt := Nat.mod_lt (a.val + 1) (by omega : 0 < b.val)
      omega
    simp [pVec, a', ha'_ne_a, ha'_ne_b, hab_ne.symm]
  · dsimp only
    have ha0 : a = ⟨0, by omega⟩ := Fin.ext h1.1
    have hb1 : b = ⟨1, by omega⟩ := Fin.ext h1.2
    rw [ha0, hb1]
    simp [pVec, Fin.ext_iff]
  · dsimp only
    have ha1 : a = ⟨1, by omega⟩ := Fin.ext h2.1
    have hb2 : b = ⟨2, by omega⟩ := Fin.ext h2.2
    rw [ha1, hb2]
    simp [pVec, Fin.ext_iff]
  · dsimp only
    have h02 : a.val = 0 ∧ b.val = 2 := by omega
    have ha0 : a = ⟨0, by omega⟩ := Fin.ext h02.1
    have hb2 : b = ⟨2, by omega⟩ := Fin.ext h02.2
    rw [ha0, hb2]
    simp [pVec, Fin.ext_iff]

private def supp {m : Nat} (α : Word m) : Finset (Fin m) :=
  Finset.univ.filter (fun r => α r ≠ 0)

private lemma supp_nonempty {m : Nat} (α : Word m) (hα : α ≠ 0) : (supp α).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply hα
  funext r
  by_contra hr
  have : r ∈ supp α := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
  rw [h] at this
  exact Finset.notMem_empty r this

private lemma card_two_eq_pair {m : Nat} {S : Finset (Fin m)} (h2 : S.card = 2) :
    let hne : S.Nonempty := Finset.card_pos.mp (by omega)
    S.min' hne < S.max' hne ∧ S = {S.min' hne, S.max' hne} := by
  intro hne
  have hle : S.min' hne ≤ S.max' hne := Finset.min'_le _ _ (Finset.max'_mem S hne)
  have hne_mm : S.min' hne ≠ S.max' hne := by
    intro heq
    have hsub : S ⊆ {S.min' hne} := by
      intro x hx
      have h1 := Finset.min'_le S x hx
      have h2' := Finset.le_max' S x hx
      rw [← heq] at h2'
      exact Finset.mem_singleton.mpr (le_antisymm h2' h1)
    have hc := Finset.card_le_card hsub
    simp [h2] at hc
  have hlt : S.min' hne < S.max' hne := lt_of_le_of_ne hle hne_mm
  have hsub2 : ({S.min' hne, S.max' hne} : Finset (Fin m)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.min'_mem S hne
    · exact Finset.max'_mem S hne
  have hcard2 : ({S.min' hne, S.max' hne} : Finset (Fin m)).card = 2 := Finset.card_pair hne_mm
  exact ⟨hlt, (Finset.eq_of_subset_of_card_le hsub2 (by omega)).symm⟩

private def Q3 {m : Nat} (hm : 3 ≤ m) (i : Fin (2 ^ m - 1)) : Word m :=
  let α := toMask m i
  let S := supp α
  let hne := supp_nonempty α (toMask_ne_zero m i)
  if S.card = 2 then
    let p := nextPair hm (S.min' hne) (S.max' hne)
    pVec p.1 p.2
  else
    eVec (S.min' hne)

private lemma Q3_eVec {m : Nat} (hm : 3 ≤ m) (r : Fin m) :
    Q3 hm (idxOf m (eVec r) (eVec_ne_zero r)) = eVec r := by
  unfold Q3
  dsimp only
  simp only [toMask_idxOf]
  have hs : supp (eVec r) = {r} := supp_eVec r
  have hcard : (supp (eVec r)).card = 1 := by rw [hs]; simp
  have hne2 : (supp (eVec r)).card ≠ 2 := by omega
  rw [if_neg hne2]
  have hmin : (supp (eVec r)).min' (supp_nonempty (eVec r) (eVec_ne_zero r)) = r := by
    set x := (supp (eVec r)).min' (supp_nonempty (eVec r) (eVec_ne_zero r))
    have hmem : x ∈ supp (eVec r) := Finset.min'_mem _ _
    rw [hs, Finset.mem_singleton] at hmem
    exact hmem
  rw [hmin]

private lemma Q3_pVec {m : Nat} (hm : 3 ≤ m) (a b : Fin m) (hab : a < b) :
    Q3 hm (idxOf m (pVec a b) (pVec_ne_zero a b (ne_of_lt hab))) =
      pVec (nextPair hm a b).1 (nextPair hm a b).2 := by
  unfold Q3
  dsimp only
  simp only [toMask_idxOf]
  have hs : supp (pVec a b) = {a, b} := supp_pVec a b (ne_of_lt hab)
  have hcard : (supp (pVec a b)).card = 2 := by rw [hs]; exact Finset.card_pair (ne_of_lt hab)
  rw [if_pos hcard]
  have hne := supp_nonempty (pVec a b) (pVec_ne_zero a b (ne_of_lt hab))
  have hmin : (supp (pVec a b)).min' hne = a := by
    apply le_antisymm
    · exact Finset.min'_le _ a (by rw [hs]; simp)
    · set x := (supp (pVec a b)).min' hne
      have hmem : x ∈ supp (pVec a b) := Finset.min'_mem _ _
      rw [hs, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · rw [h]
      · rw [h]; exact le_of_lt hab
  have hmax : (supp (pVec a b)).max' hne = b := by
    apply le_antisymm
    · set x := (supp (pVec a b)).max' hne
      have hmem : x ∈ supp (pVec a b) := Finset.max'_mem _ _
      rw [hs, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · rw [h]; exact le_of_lt hab
      · rw [h]
    · exact Finset.le_max' _ b (by rw [hs]; simp)
  rw [hmin, hmax]

private def readerSite {m : Nat} (hm : 3 ≤ m) (j : Fin (2 ^ m - 1)) (r : Fin m) :
    Fin (2 ^ m - 1) :=
  let α := toMask m j
  let S := supp α
  let hne := supp_nonempty α (toMask_ne_zero m j)
  let r0 := S.min' hne
  if h : r ∈ S ∧ r0 < r then
    let p := prevPair hm r0 r
    idxOf m (pVec p.1 p.2) (pVec_ne_zero p.1 p.2 (ne_of_lt (prevPair_lt hm r0 r h.2)))
  else
    idxOf m (eVec r) (eVec_ne_zero r)

private def R3 {m : Nat} (hm : 3 ≤ m) (j : Fin (2 ^ m - 1)) : Finset (Fin (2 ^ m - 1)) :=
  let α := toMask m j
  let S := supp α
  let hne := supp_nonempty α (toMask_ne_zero m j)
  let r0 := S.min' hne
  (Finset.univ.erase r0).image (readerSite hm j)

private lemma Q3_readerSite_out {m : Nat} (hm : 3 ≤ m) (j : Fin (2 ^ m - 1)) (r : Fin m)
    (hr : r ∉ supp (toMask m j)) :
    Q3 hm (readerSite hm j r) = eVec r := by
  unfold readerSite
  dsimp only
  have hnot : ¬ (r ∈ supp (toMask m j) ∧ (supp (toMask m j)).min' (supp_nonempty _ (toMask_ne_zero m j)) < r) :=
    fun h => hr h.1
  rw [dif_neg hnot]
  exact Q3_eVec hm r

private lemma Q3_readerSite_in {m : Nat} (hm : 3 ≤ m) (j : Fin (2 ^ m - 1)) (r : Fin m)
    (hr : r ∈ supp (toMask m j))
    (hne_r0 : r ≠ (supp (toMask m j)).min' (supp_nonempty _ (toMask_ne_zero m j))) :
    Q3 hm (readerSite hm j r) =
      pVec ((supp (toMask m j)).min' (supp_nonempty _ (toMask_ne_zero m j))) r := by
  let hne := supp_nonempty (toMask m j) (toMask_ne_zero m j)
  let r0 := (supp (toMask m j)).min' hne
  have hlt : r0 < r := lt_of_le_of_ne (Finset.min'_le _ r hr) hne_r0.symm
  unfold readerSite
  dsimp only
  rw [dif_pos ⟨hr, hlt⟩]
  have hplt := prevPair_lt hm r0 r hlt
  rw [Q3_pVec hm _ _ hplt, nextPair_prevPair hm r0 r hlt]

private lemma upper_m3 (m : Nat) (hm : 3 ≤ m) :
    ∃ (D : Fin (2 ^ m - 1) → Finset (Fin (2 ^ m - 1))) (Q : Fin (2 ^ m - 1) → Word m),
      (∀ i, i ∉ D i) ∧
      (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
      (∀ j, readersDef (2 ^ m - 1) D j = m - 1) ∧
      wiresDef (2 ^ m - 1) D = (2 ^ m - 1) * (m - 1) ∧
      (∀ U, uniformDef (2 ^ m - 1) m D Q U ↔ U = Finset.univ) := by
  apply upper_from_QR m (Q3 hm) (R3 hm)
  · intro i
    unfold Q3
    dsimp only
    split_ifs with h2
    · have hne := supp_nonempty (toMask m i) (toMask_ne_zero m i)
      have hlt := (card_two_eq_pair h2).1
      have hplt := nextPair_lt hm _ _ hlt
      rw [supp_pVec _ _ (ne_of_lt hplt)]
      exact Finset.card_le_two
    · rw [supp_eVec]
      simp
  · intro j
    unfold R3
    dsimp only
    let hne := supp_nonempty (toMask m j) (toMask_ne_zero m j)
    let r0 := (supp (toMask m j)).min' hne
    have hinj : Set.InjOn (readerSite hm j) (Finset.univ.erase r0 : Set (Fin m)) := by
      intro r1 hr1 r2 hr2 heq
      have hr1ne : r1 ≠ r0 := (Finset.mem_erase.mp hr1).1
      have hr2ne : r2 ≠ r0 := (Finset.mem_erase.mp hr2).1
      have hQeq := congrArg (Q3 hm) heq
      by_cases h1 : r1 ∈ supp (toMask m j) <;> by_cases h2 : r2 ∈ supp (toMask m j)
      · rw [Q3_readerSite_in hm j r1 h1 hr1ne, Q3_readerSite_in hm j r2 h2 hr2ne] at hQeq
        have hv := congrFun hQeq r1
        simp only [pVec, hr1ne, if_false, zero_add, if_pos rfl] at hv
        by_contra hne12
        simp [hne12] at hv
      · rw [Q3_readerSite_in hm j r1 h1 hr1ne, Q3_readerSite_out hm j r2 h2] at hQeq
        have hc := congrArg (fun w => (supp w).card) hQeq
        change (Finset.univ.filter (fun t => pVec r0 r1 t ≠ 0)).card =
          (Finset.univ.filter (fun t => eVec r2 t ≠ 0)).card at hc
        rw [supp_pVec r0 r1 hr1ne.symm, Finset.card_pair hr1ne.symm, supp_eVec] at hc
        simp at hc
      · rw [Q3_readerSite_out hm j r1 h1, Q3_readerSite_in hm j r2 h2 hr2ne] at hQeq
        have hc := congrArg (fun w => (supp w).card) hQeq
        change (Finset.univ.filter (fun t => eVec r1 t ≠ 0)).card =
          (Finset.univ.filter (fun t => pVec r0 r2 t ≠ 0)).card at hc
        rw [supp_pVec r0 r2 hr2ne.symm, Finset.card_pair hr2ne.symm, supp_eVec] at hc
        simp at hc
      · rw [Q3_readerSite_out hm j r1 h1, Q3_readerSite_out hm j r2 h2] at hQeq
        have hv := congrFun hQeq r1
        simp only [eVec, if_pos rfl] at hv
        by_contra hne12
        simp [hne12] at hv
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  · intro j
    unfold Q3
    dsimp only
    split_ifs with h2
    · obtain ⟨hlt, hpair⟩ := card_two_eq_pair h2
      have hαeq : toMask m j =
          pVec ((supp (toMask m j)).min' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))
            ((supp (toMask m j)).max' (supp_nonempty (toMask m j) (toMask_ne_zero m j))) := by
        funext r
        by_cases hr : r ∈ supp (toMask m j)
        · have hr1 : toMask m j r = 1 := (zmod2_ne_zero_iff _).mp (Finset.mem_filter.mp hr).2
          rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with hr' | hr'
          · rw [hr1, hr']; simp [pVec, ne_of_lt hlt]
          · rw [hr1, hr']; simp [pVec, (ne_of_lt hlt).symm]
        · have hr0 : toMask m j r = 0 := by
            by_contra h
            exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ r, h⟩)
          rw [hpair, Finset.mem_insert, Finset.mem_singleton, not_or] at hr
          rw [hr0]; simp [pVec, hr.1, hr.2]
      calc
        dot (toMask m j)
            (pVec (nextPair hm ((supp (toMask m j)).min' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))
              ((supp (toMask m j)).max' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))).1
              (nextPair hm ((supp (toMask m j)).min' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))
              ((supp (toMask m j)).max' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))).2)
          = dot (pVec ((supp (toMask m j)).min' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))
              ((supp (toMask m j)).max' (supp_nonempty (toMask m j) (toMask_ne_zero m j))))
              (pVec (nextPair hm ((supp (toMask m j)).min' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))
              ((supp (toMask m j)).max' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))).1
              (nextPair hm ((supp (toMask m j)).min' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))
              ((supp (toMask m j)).max' (supp_nonempty (toMask m j) (toMask_ne_zero m j)))).2) :=
            congrArg (fun w => dot w _) hαeq
        _ = 1 := nextPair_dot_one hm _ _ hlt
    · rw [dot_eVec]
      have hmem := Finset.min'_mem (supp (toMask m j)) (supp_nonempty (toMask m j) (toMask_ne_zero m j))
      exact (zmod2_ne_zero_iff _).mp (Finset.mem_filter.mp hmem).2
  · intro j i hi
    unfold R3 at hi
    dsimp only at hi
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
    set α := toMask m j
    set hne := supp_nonempty α (toMask_ne_zero m j)
    have hrne : r ≠ (supp α).min' hne := (Finset.mem_erase.mp hr).1
    by_cases hrs : r ∈ supp α
    · rw [Q3_readerSite_in hm j r hrs hrne, dot_pVec]
      have h1 : α ((supp α).min' hne) = 1 :=
        (zmod2_ne_zero_iff _).mp (Finset.mem_filter.mp (Finset.min'_mem (supp α) hne)).2
      have h2 : α r = 1 := (zmod2_ne_zero_iff _).mp (Finset.mem_filter.mp hrs).2
      change α ((supp α).min' hne) + α r = 0
      rw [h1, h2]
      decide
    · rw [Q3_readerSite_out hm j r hrs, dot_eVec]
      by_contra h
      exact hrs (Finset.mem_filter.mpr ⟨Finset.mem_univ r, h⟩)
  · intro j β hβ
    set α := toMask m j
    set hne := supp_nonempty α (toMask_ne_zero m j)
    set r0 := (supp α).min' hne
    have hmem_r0 : r0 ∈ supp α := Finset.min'_mem (supp α) hne
    have hβout : ∀ r : Fin m, r ∉ supp α → β r = 0 := by
      intro r hr
      have hrne : r ≠ r0 := fun h => hr (h ▸ hmem_r0)
      have hmem : readerSite hm j r ∈ R3 hm j :=
        Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hrne, Finset.mem_univ r⟩)
      have h0 := hβ _ hmem
      rwa [Q3_readerSite_out hm j r hr, dot_eVec] at h0
    have hβin : ∀ r : Fin m, r ∈ supp α → β r = β r0 := by
      intro r hr
      by_cases hrne : r = r0
      · rw [hrne]
      · have hmem : readerSite hm j r ∈ R3 hm j :=
          Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hrne, Finset.mem_univ r⟩)
        have h0 := hβ _ hmem
        rw [Q3_readerSite_in hm j r hr hrne, dot_pVec] at h0
        change β r0 + β r = 0 at h0
        have := congrArg (fun t => β r0 + t) h0
        simpa [← add_assoc, zmod2_add_self] using this
    rcases zmod2_cases (β r0) with hb0 | hb1
    · left
      funext r
      by_cases hr : r ∈ supp α
      · simp [hβin r hr, hb0]
      · simp [hβout r hr]
    · right
      funext r
      by_cases hr : r ∈ supp α
      · rw [hβin r hr, hb1]
        exact ((zmod2_ne_zero_iff _).mp (Finset.mem_filter.mp hr).2).symm
      · rw [hβout r hr]
        by_contra hne0
        exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ r, Ne.symm hne0⟩)

theorem main :
    let Word := fun k : Nat => Fin k → ZMod 2
    let localRule := fun (n : Nat) (D : Fin n → Finset (Fin n)) (T : Fin n → Word n → ZMod 2) =>
      ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y
    let observed := fun (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
        (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) (r : Fin m) =>
      let x := fun i : Fin n => if h : i ∈ U then z ⟨i,h⟩ else b i
      ∑ i, (x i + T i x) * Q i r
    let uniform := fun (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
        (U : Finset (Fin n)) =>
      ∀ T, localRule n D T → ∀ b v,
        2^m * Nat.card {z : U → ZMod 2 // observed n m Q U T b z = v} = 2^U.card
    let readers := fun (n : Nat) (D : Fin n → Finset (Fin n)) (j : Fin n) =>
      (Finset.univ.filter (fun i => j ∈ D i)).card
    let wires := fun (n : Nat) (D : Fin n → Finset (Fin n)) => ∑ i, (D i).card
    ∀ m : Nat, 1 ≤ m →
      let N := 2^m - 1
      (∃ (D : Fin N → Finset (Fin N)) (Q : Fin N → Word m),
        (∀ i, i ∉ D i) ∧
        (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
        (∀ j, readers N D j = m-1) ∧ wires N D = N*(m-1) ∧
        (∀ U, uniform N m D Q U ↔ U = Finset.univ)) ∧
      (∀ (n : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m) (W : Finset (Fin n)),
        W.card = N → uniform n m D Q Finset.univ →
        (∀ j ∈ W, ¬ uniform n m D Q (Finset.univ.erase j)) →
        N ≤ n ∧ (∀ j ∈ W, m-1 ≤ readers n D j) ∧ N*(m-1) ≤ wires n D) := by
  intro Word localRule observed uniform readers wires m hm N
  constructor
  · by_cases hm1 : m = 1
    · subst hm1
      exact upper_m1
    · by_cases hm2 : m = 2
      · subst hm2
        exact upper_m2
      · exact upper_m3 m (by omega)
  · intro n D Q W hW hunif hcrit
    exact lower_bound m hm n D Q W hW hunif hcrit

end PEqualNP.Outside.L_lib_1095_aux

theorem PEqualNP.Outside.L_lib_1095 :
let Word := fun k : Nat => Fin k → ZMod 2
let localRule := fun (n : Nat) (D : Fin n → Finset (Fin n)) (T : Fin n → Word n → ZMod 2) =>
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y
let observed := fun (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
    (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) (r : Fin m) =>
  let x := fun i : Fin n => if h : i ∈ U then z ⟨i,h⟩ else b i
  ∑ i, (x i + T i x) * Q i r
let uniform := fun (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) =>
  ∀ T, localRule n D T → ∀ b v,
    2^m * Nat.card {z : U → ZMod 2 // observed n m Q U T b z = v} = 2^U.card
let readers := fun (n : Nat) (D : Fin n → Finset (Fin n)) (j : Fin n) =>
  (Finset.univ.filter (fun i => j ∈ D i)).card
let wires := fun (n : Nat) (D : Fin n → Finset (Fin n)) => ∑ i, (D i).card
∀ m : Nat, 1 ≤ m →
  let N := 2^m - 1
  (∃ (D : Fin N → Finset (Fin N)) (Q : Fin N → Word m),
    (∀ i, i ∉ D i) ∧
    (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
    (∀ j, readers N D j = m-1) ∧ wires N D = N*(m-1) ∧
    (∀ U, uniform N m D Q U ↔ U = Finset.univ)) ∧
  (∀ (n : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m) (W : Finset (Fin n)),
    W.card = N → uniform n m D Q Finset.univ →
    (∀ j ∈ W, ¬ uniform n m D Q (Finset.univ.erase j)) →
    N ≤ n ∧ (∀ j ∈ W, m-1 ≤ readers n D j) ∧ N*(m-1) ≤ wires n D) :=
  PEqualNP.Outside.L_lib_1095_aux.main

