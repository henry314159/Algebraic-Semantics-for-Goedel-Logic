import GoedelLogic.ChainSoundness
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs

-- Define the rational unit interval
def Q := Set.Icc (0 : ℚ) 1

theorem zero_memQ : (0 : ℚ) ∈ Q := by
  apply And.intro
  · exact le_rfl
  · exact zero_le_one

theorem one_memQ : (1 : ℚ) ∈ Q := by
  apply And.intro
  · exact zero_le_one
  · exact le_rfl

lemma max_oneQ {x : Q} : max ⟨1, one_memQ⟩ x = ⟨1, one_memQ⟩ := by
  rw [le_antisymm_iff]
  have h1 : (1 : ℚ) ≤ (1 : ℚ) := by simp
  have hx : (x : ℚ) ∈ Q := by simp
  apply And.intro
  · exact max_le h1 hx.right
  · exact le_sup_left

-- Need to show that the mean of q1 and q2 is in Q, for constructing the embedding into Q
theorem mean_memQ (q1 q2 : Q) : ((q1:ℚ)/2) + ((q2:ℚ)/2) ∈ Q := by
  have hq1 : (q1 : ℚ) ∈ Q := by simp
  have hq1' : 0 ≤ (q1 : ℚ)/2 := @Rat.div_nonneg (q1 : ℚ) 2 hq1.left zero_le_two
  have hq1'' : (q1 : ℚ)/2 ≤ 1/2 := by
    apply @Rat.le_of_mul_le_mul_left _ _ 2
    · rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero]
      exact hq1.right
    · simp
  have hq2 : (q2 : ℚ) ∈ Q := by simp
  have hq2' : 0 ≤ (q2 : ℚ)/2 := @Rat.div_nonneg (q2 : ℚ) 2 hq2.left zero_le_two
  have hq2'' : (q2 : ℚ)/2 ≤ 1/2 := by
    apply @Rat.le_of_mul_le_mul_left _ _ 2
    · rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero]
      exact hq2.right
    · simp
  apply And.intro
  · exact @Rat.add_nonneg ((q1:ℚ)/2) ((q2:ℚ)/2) hq1' hq2'
  · rw [← add_halves 1]
    exact add_le_add hq1'' hq2''

def mean (q1 : Q) (q2 : Q) : Q := ⟨((q1:ℚ)/2) + ((q2:ℚ)/2), mean_memQ q1 q2⟩

-- Define the Heyting implication for Q
def himpQ (a b : Q) : Q := if a ≤ b then ⟨1, one_memQ⟩ else b

-- Show that Q is an LAlgebra
instance : LAlgebra Q := {
  top := ⟨1, one_memQ⟩
  le_top := λ a => by
    have ha : (a : ℚ) ∈ Q := by simp
    exact ha.right
  himp := himpQ
  le_himp_iff := λ a1 a2 a3 => by
    simp [himpQ]
    apply Iff.intro
    · intro h
      by_cases hCase : a2 ≤ a3
      · apply Or.intro_right
        exact hCase
      · apply Or.intro_left
        rw [if_neg hCase] at h
        exact h
    · intro h
      split_ifs
      · have ha : (a1 : ℚ) ∈ Q := by simp
        exact ha.right
      · cases h
        · assumption
        · by_contra
          rename_i h1 h2
          exact h1 h2
  bot := ⟨0, zero_memQ⟩
  bot_le := λ a => by
    have ha : (a : ℚ) ∈ Q := by simp
    exact ha.left
  compl := λ q => himpQ q ⟨0, zero_memQ⟩
  himp_bot := λ q => by rfl
  l_axiom := λ q1 q2 => by
    simp [himpQ]
    split_ifs
    · simp
    · exact max_oneQ
    · rw [max_comm]
      exact max_oneQ
    · by_contra
      have h : q1 ≤ q2 ∨ q2 ≤ q1 := le_total _ _
      cases h
      · rename_i h1 _ h3
        exact h1 h3
      · rename_i _ h2 h3
        exact h2 h3 }

def rational_unit_interval_sem_conseq (Γ : Set Formula) (ϕ : Formula): Prop :=
  ∀ (I : Var → Q), set_true_in_alg_model I Γ → true_in_alg_model I ϕ

theorem soundness_rational_unit_interval {Γ : Set Formula} (ϕ : Formula) :
  Nonempty (Γ ⊢ ϕ) → rational_unit_interval_sem_conseq Γ ϕ :=
  by
    intro Htheorem
    apply soundness_lalg ϕ at Htheorem
    intro _ h
    exact Htheorem _ _ h
