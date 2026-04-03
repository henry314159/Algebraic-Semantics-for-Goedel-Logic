import GoedelLogic.ChainSoundness
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs

-- Define the rational unit interval
def Q := Set.Icc (0 : ℚ) 1

theorem zero_mem_Q : (0 : ℚ) ∈ Q := by
  apply And.intro
  · exact le_rfl
  · exact zero_le_one

theorem one_mem_Q : (1 : ℚ) ∈ Q := by
  apply And.intro
  · exact zero_le_one
  · exact le_rfl

theorem max_one_Q {x : Q} : max ⟨1, one_mem_Q⟩ x = ⟨1, one_mem_Q⟩ := by
  rw [le_antisymm_iff]
  have h1 : (1 : ℚ) ≤ (1 : ℚ) := by simp
  have hx : (x : ℚ) ∈ Q := by simp
  apply And.intro
  · exact max_le h1 hx.right
  · exact le_sup_left

-- Need to show that the mean of q1 and q2 is in Q, for constructing the embedding into Q
theorem mean_mem_Q (q1 q2 : Q) : ((q1:ℚ)/2) + ((q2:ℚ)/2) ∈ Q := by
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

def mean (q1 : Q) (q2 : Q) : Q := ⟨((q1:ℚ)/2) + ((q2:ℚ)/2), mean_mem_Q q1 q2⟩

theorem mean_le_mean (a : Q) (b : Q) (c : Q) (d : Q) : a ≤ c → b ≤ d → mean a b ≤ mean c d := by
  intro hac hbd
  have hab : @LE.le ℚ Rat.instLE (↑a / 2) (↑c / 2) := by
    apply @Rat.le_of_mul_le_mul_left _ _ 2
    · rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero]
      exact hac
    · simp
  have hbd : @LE.le ℚ Rat.instLE (↑b / 2) (↑d / 2) := by
    apply @Rat.le_of_mul_le_mul_left _ _ 2
    · rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero]
      exact hbd
    · simp
  unfold mean
  simp
  apply add_le_add
  exact hab
  exact hbd

theorem mean_lt_mean_left (a : Q) (b : Q) (c : Q) (d : Q) : a < c → b ≤ d → mean a b < mean c d := by
  intro hac hbd
  have hac : @LT.lt ℚ Rat.instLT (↑a / 2) (↑c / 2) := by
    apply @Rat.lt_of_mul_lt_mul_left _ _ 2
    · rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero]
      exact hac
    · simp
  have hbd : @LE.le ℚ Rat.instLE (↑b / 2) (↑d / 2) := by
    apply @Rat.le_of_mul_le_mul_left _ _ 2
    · rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero]
      exact hbd
    · simp
  unfold mean
  simp
  by_cases hbd' : (b:ℚ)/2 = (d:ℚ)/2
  · rw [hbd']
    apply add_lt_add_left
    exact hac
  · have hbd : (b:ℚ)/2 < (d:ℚ)/2 := by
      rw [lt_iff_le_and_ne]
      exact And.intro hbd hbd'
    apply add_lt_add
    exact hac
    exact hbd

theorem mean_lt_mean_right (a : Q) (b : Q) (c : Q) (d : Q) : a ≤ c → b < d → mean a b < mean c d := by
  intro hac hbd
  have hac : @LE.le ℚ Rat.instLE (↑a / 2) (↑c / 2) := by
    apply @Rat.le_of_mul_le_mul_left _ _ 2
    · rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero]
      exact hac
    · simp
  have hbd : @LT.lt ℚ Rat.instLT (↑b / 2) (↑d / 2) := by
    apply @Rat.lt_of_mul_lt_mul_left _ _ 2
    · rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero]
      exact hbd
    · simp
  unfold mean
  simp
  by_cases hac' : (a:ℚ)/2 = (c:ℚ)/2
  · rw [hac']
    apply add_lt_add_right
    exact hbd
  · have hac : (a:ℚ)/2 < (c:ℚ)/2 := by
      rw [lt_iff_le_and_ne]
      exact And.intro hac hac'
    apply add_lt_add
    exact hac
    exact hbd

theorem mean_self (a : Q) : a = mean a a := by
  unfold mean
  simp

theorem le_mean (a : Q) (b : Q) (c : Q) : a ≤ b → a ≤ c → a ≤ mean b c := by
  intro hab hac
  rw [mean_self a]
  exact mean_le_mean a a b c hab hac

theorem lt_mean (a : Q) (b : Q) (c : Q) : a ≤ b → a < c → a < mean b c := by
  intro hab hac
  rw [mean_self a]
  exact mean_lt_mean_right a a b c hab hac

theorem mean_le (a : Q) (b : Q) (c : Q) : a ≤ c → b ≤ c → mean a b ≤ c := by
  intro hac hbc
  rw [mean_self c]
  exact mean_le_mean a b c c hac hbc

theorem mean_lt (a : Q) (b : Q) (c : Q) : a < c → b ≤ c → mean a b < c := by
  intro hab hac
  rw [mean_self c]
  exact mean_lt_mean_left a b c c hab hac

theorem mean_eq_one (a : Q) (b : Q) : mean a b = ⟨1, one_mem_Q⟩ ↔ a = ⟨1, one_mem_Q⟩ ∧ b = ⟨1, one_mem_Q⟩ := by
  apply Iff.intro
  · intro h
    unfold mean at h
    simp at h
    have h : 2 * ((a:ℚ)/2+(b:ℚ)/2)=2 := by simp [h]
    have h : 2*((a:ℚ)/2) + 2*((b:ℚ)/2)=2 := by rw [← mul_add, h]
    have h : (a:ℚ) + (b:ℚ) = 2 := by
      rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero] at h
      exact h

    have ha : (a:ℚ) ∈ Q := by simp
    have ha : (a:ℚ) ≤ 1 := ha.right
    have hb : (b:ℚ) ∈ Q := by simp
    have hb : (b:ℚ) ≤ 1 := hb.right

    have temp : (a:ℚ) = 2-(b:ℚ) := by
      rw [eq_sub_iff_add_eq]
      exact h
    have hb' : 2 - (b:ℚ) ≤ 1 := by
      have temp : 2-(b:ℚ) = (a:ℚ) := by simp only [temp]
      have temp : 2-(b:ℚ) ≤ (a:ℚ) := by simp [temp]
      exact le_trans temp ha
    have hb' : 1 ≤ (b:ℚ) := by
      simp at hb'
      have temp : 2 - 1 ≤ (b:ℚ) := by
        rw [sub_le_iff_le_add, add_comm]
        exact hb'
      have : (2:ℚ)-1=1 := by norm_cast
      rw [this] at temp
      exact temp
    have hb'' : (b:ℚ) = 1 := by
      apply Rat.le_antisymm
      exact hb
      exact hb'
    have hb'' : b = ⟨1, one_mem_Q⟩ := by
      apply Subtype.ext
      exact hb''

    have temp : (b:ℚ) = 2-(a:ℚ) := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact h
    have ha' : 2 - (a:ℚ) ≤ 1 := by
      have temp : 2-(a:ℚ) = (b:ℚ) := by simp only [temp]
      have temp : 2-(a:ℚ) ≤ (b:ℚ) := by simp [temp]
      exact le_trans temp hb
    have ha' : 1 ≤ (a:ℚ) := by
      simp at ha'
      have temp : 2 - 1 ≤ (a:ℚ) := by
        rw [sub_le_iff_le_add, add_comm]
        exact ha'
      have : (2:ℚ)-1=1 := by norm_cast
      rw [this] at temp
      exact temp
    have ha'' : (a:ℚ) = 1 := by
      apply Rat.le_antisymm
      exact ha
      exact ha'
    have ha'' : a = ⟨1, one_mem_Q⟩ := by
      apply Subtype.ext
      exact ha''

    exact And.intro ha'' hb''
  · intro h
    apply Eq.symm
    rw [h.right, h.left]
    exact mean_self ⟨1, one_mem_Q⟩

theorem mean_eq_zero (a : Q) (b : Q) : mean a b = ⟨0, zero_mem_Q⟩ ↔ a = ⟨0, zero_mem_Q⟩ ∧ b = ⟨0, one_mem_Q⟩ := by
  apply Iff.intro
  · intro h
    unfold mean at h
    simp at h
    have h : 2 * ((a:ℚ)/2+(b:ℚ)/2)=0 := by simp [h]
    have h : 2*((a:ℚ)/2) + 2*((b:ℚ)/2)=0 := by rw [← mul_add, h]
    have h : (a:ℚ) + (b:ℚ) = 0 := by
      rw [mul_comm, Rat.div_mul_cancel two_ne_zero, mul_comm, Rat.div_mul_cancel two_ne_zero] at h
      exact h

    have ha : (a:ℚ) ∈ Q := by simp
    have ha : 0 ≤ (a:ℚ) := ha.left
    have hb : (b:ℚ) ∈ Q := by simp
    have hb : 0 ≤ (b:ℚ) := hb.left

    have h' : (a:ℚ) = -(b:ℚ) := by
      rw [add_eq_zero_iff_eq_neg] at h
      exact h

    have hb' : (a:ℚ) ≤ -(b:ℚ) := by
      rw [le_iff_eq_or_lt]
      exact Or.inl h'
    have hb' : 0 ≤ -(b:ℚ) := le_trans ha hb'
    rw [le_neg] at hb'
    simp at hb'
    have hb'' : (b:ℚ) = 0 := by
      apply Rat.le_antisymm
      exact hb'
      exact hb
    have hb'' : b = ⟨0, zero_mem_Q⟩ := by
      apply Subtype.ext
      exact hb''

    have h' : (b:ℚ)=-(a:ℚ) := by
      rw [add_eq_zero_iff_neg_eq] at h
      apply Eq.symm
      exact h

    have ha' : (b:ℚ) ≤ -(a:ℚ) := by
      rw [le_iff_eq_or_lt]
      exact Or.inl h'
    have hb' : 0 ≤ -(a:ℚ) := le_trans hb ha'
    rw [le_neg] at ha'
    simp at hb'
    have ha'' : (a:ℚ) = 0 := by
      apply Rat.le_antisymm
      exact hb'
      exact ha
    have ha'' : a = ⟨0, zero_mem_Q⟩ := by
      apply Subtype.ext
      exact ha''

    exact And.intro ha'' hb''
  · intro h
    apply Eq.symm
    rw [h.right, h.left]
    exact mean_self ⟨0, zero_mem_Q⟩

-- Define the Heyting implication for Q
def himp_Q (a b : Q) : Q := if a ≤ b then ⟨1, one_mem_Q⟩ else b

-- Show that Q is an LAlgebra
instance : LAlgebra Q := {
  top := ⟨1, one_mem_Q⟩
  le_top := λ a => by
    have ha : (a : ℚ) ∈ Q := by simp
    exact ha.right
  himp := himp_Q
  le_himp_iff := λ a1 a2 a3 => by
    simp [himp_Q]
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
  bot := ⟨0, zero_mem_Q⟩
  bot_le := λ a => by
    have ha : (a : ℚ) ∈ Q := by simp
    exact ha.left
  compl := λ q => himp_Q q ⟨0, zero_mem_Q⟩
  himp_bot := λ q => by rfl
  l_axiom := λ q1 q2 => by
    simp [himp_Q]
    split_ifs
    · simp
    · exact max_one_Q
    · rw [max_comm]
      exact max_one_Q
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
