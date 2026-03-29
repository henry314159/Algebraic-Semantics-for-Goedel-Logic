import GoedelLogic.ChainSoundness
import Mathlib.Data.Real.Basic

-- Define the real unit interval
def R := Set.Icc (0 : ℝ) 1

theorem zero_mem_R : (0 : ℝ) ∈ R := by
  apply And.intro
  · exact le_rfl
  · exact zero_le_one

theorem one_mem_R : (1 : ℝ) ∈ R := by
  apply And.intro
  · exact zero_le_one
  · exact le_rfl

-- Define Heyting implication
noncomputable def himp_R (a b : R) : R := if a ≤ b then ⟨1, one_mem_R⟩ else b

lemma max_one_R {x : R} : max ⟨1, one_mem_R⟩ x = ⟨1, one_mem_R⟩ := by
  rw [le_antisymm_iff]
  have hx : (x : ℝ) ∈ R := by simp
  apply And.intro
  · exact max_le le_rfl hx.right
  · exact le_sup_left

-- Show that R is an LAlgebra
noncomputable instance : LAlgebra R := {
  top := ⟨1, one_mem_R⟩
  le_top := λ a => by
    have ha : (a : ℝ) ∈ R := by simp
    exact ha.right
  himp := himp_R
  le_himp_iff := λ a1 a2 a3 => by
    simp [himp_R]
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
      · have ha : (a1 : ℝ) ∈ R := by simp
        exact ha.right
      · cases h
        · assumption
        · by_contra
          rename_i h1 h2
          exact h1 h2
  bot := ⟨0, zero_mem_R⟩
  bot_le := λ a => by
    have ha : (a : ℝ) ∈ R := by simp
    exact ha.left
  compl := λ q => himp_R q ⟨0, zero_mem_R⟩
  himp_bot := λ q => rfl
  l_axiom := λ q1 q2 => by
    simp [himp_R]
    split_ifs
    · simp
    · exact max_one_R
    · rw [max_comm]
      exact max_one_R
    · by_contra
      have h : q1 ≤ q2 ∨ q2 ≤ q1 := le_total _ _
      cases h
      · rename_i h1 _ h3
        exact h1 h3
      · rename_i _ h2 h3
        exact h2 h3
}

def real_unit_interval_sem_conseq (Γ : Set Formula) (ϕ : Formula): Prop :=
  ∀ (I : Var → R), set_true_in_alg_model I Γ → true_in_alg_model I ϕ

theorem soundness_real_unit_interval {Γ : Set Formula} (ϕ : Formula) :
  Nonempty (Γ ⊢ ϕ) → real_unit_interval_sem_conseq Γ ϕ :=
  by
    intro Htheorem
    apply soundness_lalg ϕ at Htheorem
    intro _ h
    exact Htheorem _ _ h
