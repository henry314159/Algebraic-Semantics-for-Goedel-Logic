import GoedelLogic.RationalUnitIntervalCompleteness
import GoedelLogic.RealUnitIntervalSoundness
import Mathlib.Data.Rat.Cast.Order

variable {α : Type} [LAlgebra α]
variable {Γ : Set Formula}
variable {F : Set (Quotient (@setoid_formula Γ))}

theorem q_mem_R (q : Q) : (q : ℝ) ∈ R := by
  have h : (q : ℚ) ∈ Q := by simp
  apply And.intro
  · exact_mod_cast h.left
  · exact_mod_cast h.right

-- The inclusion map Q → R
noncomputable def incl (q : Q) : R := ⟨Rat.castOrderEmbedding q, q_mem_R q⟩

lemma zero_eq_zero :
  ((⟨0, zero_mem_Q⟩ : Q) : ℝ) = ((⟨0, zero_mem_R⟩ : R) : ℝ) := by simp

lemma one_eq_one :
  ((⟨1, one_mem_Q⟩ : Q) : ℝ) = ((⟨1, one_mem_R⟩ : R) : ℝ) := by simp

lemma incl_top : incl Top.top = Top.top := by
  unfold incl
  apply Subtype.ext
  exact one_eq_one

lemma incl_bot : incl Bot.bot = Bot.bot := by
  unfold incl
  apply Subtype.ext
  exact zero_eq_zero

lemma incl_inf : ∀ (a b : Q), incl (a ⊓ b) = incl a ⊓ incl b := by
  intro _ _
  unfold incl
  simp [min, SemilatticeInf.inf, Lattice.inf]

lemma incl_sup : ∀ (a b : Q), incl (a ⊔ b) = incl a ⊔ incl b := by
  intro _ _
  unfold incl
  simp [max, SemilatticeSup.sup]

lemma incl_to : ∀ (a b : Q), incl (a ⇨ b) = incl a ⇨ incl b := by
  intro _ _
  unfold incl
  simp [himp, himp_Q, himp_R]
  split_ifs
  · simp
  · simp

lemma incl_inj : Function.Injective incl := by
  intro _ _
  simp [incl]
  exact Subtype.ext

-- Define the valuation into R that allows us to prove completeness
noncomputable def f_r_var {hF : filter F} {f : Quotient (@setoid_filter (Quotient setoid_formula) _ _ _) → Q} (v : Var) :=
  incl (f (@filter_quot_var _ _ hF v))

noncomputable def f_r {hF : filter F} {f : Quotient (@setoid_filter (Quotient setoid_formula) _ _ _) → Q} (ϕ : Formula) :=
  incl (f (@filter_quot _ _ hF ϕ))

lemma f_r_alg_interpretation {hF : filter F} {f : Quotient (@setoid_filter (Quotient setoid_formula) _ _ _) → Q} {hf : Q_homomorphism f}:
  ∀ (ϕ : Formula), @f_r _ _ hF f ϕ =
    @AlgInterpretation R _ (f_r_var (f := f)) ϕ := by
  intro ϕ
  induction ϕ with
    | var v => rfl
    | bottom =>
        rw [f_r, filter_quot, AlgInterpretation, h_lt]
        have h1 : @Quotient.mk Formula (@setoid_formula Γ) ⊥ = Bot.bot := rfl
        have h2 : @Quotient.mk (Quotient setoid_formula) (@setoid_filter (Quotient setoid_formula) _ _ hF) Bot.bot = Bot.bot := rfl
        rw [h1, h2, hf.right.left]
        exact incl_bot
    | and ψ χ ih1 ih2 =>
        let ψModΓ := @h_lt Γ ψ
        let χModΓ := @h_lt Γ χ
        let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
        let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
        have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ∧∧χ) = and_lt ψModΓ χModΓ := rfl
        have Haux2 : Quotient.mk setoid_filter (and_lt ψModΓ χModΓ) = ψModΓModG ⊓ χModΓModG := rfl
        rw [f_r, filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2, f_r, f_r]
        have h : f (ψModΓModG ⊓ χModΓModG) = f (filter_quot ψ) ⊓ f (filter_quot χ) :=
          (hf.right.right ψModΓModG χModΓModG).right.left
        simp only [setoid_formula.eq_1, h]
        exact incl_inf (f_q ψ) (f_q χ)
    | or ψ χ ih1 ih2 =>
        let ψModΓ := @h_lt Γ ψ
        let χModΓ := @h_lt Γ χ
        let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
        let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
        have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ∨∨χ) = or_lt ψModΓ χModΓ := rfl
        have Haux2 : Quotient.mk setoid_filter (or_lt ψModΓ χModΓ) = ψModΓModG ⊔ χModΓModG := rfl
        rw [f_r, filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2, f_r, f_r]
        have h : f (ψModΓModG ⊔ χModΓModG) = f (filter_quot ψ) ⊔  f (filter_quot χ) :=
          (hf.right.right ψModΓModG χModΓModG).right.right.left
        simp only [setoid_formula.eq_1, h]
        exact incl_sup (f_q ψ) (f_q χ)
    | implication ψ χ ih1 ih2 =>
        let ψModΓ := @h_lt Γ ψ
        let χModΓ := @h_lt Γ χ
        let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
        let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
        have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ⇒χ) = to_lt ψModΓ χModΓ := rfl
        have Haux2 : Quotient.mk setoid_filter (to_lt ψModΓ χModΓ) = ψModΓModG ⇨ χModΓModG := rfl
        rw [f_r, filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2, f_r, f_r]
        have h : f (ψModΓModG ⇨ χModΓModG) = f (filter_quot ψ) ⇨  f (filter_quot χ) :=
          (hf.right.right ψModΓModG χModΓModG).right.right.right
        simp only [setoid_formula.eq_1, h]
        exact incl_to (f_q ψ) (f_q χ)

lemma real_contradicting_valuation {Γ : Set Formula} (ϕ : Formula) : ¬Nonempty (Γ ⊢ ϕ) →
  ∃ (F : Set (Quotient (@setoid_formula Γ))) (hF : prime_filter F)
    (f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ F hF.left.left) → Q),
    set_true_in_alg_model (@f_r_var Γ F hF.left.left f) Γ ∧
    ¬true_in_alg_model (@f_r_var Γ F hF.left.left f) ϕ := by
  intro notTrueInLTAlgebra
  -- use rational_contradicting_valuation lemma
  have h : ∃ (F : Set (Quotient (@setoid_formula Γ)))
    (hF : prime_filter F)
    (f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ F hF.left.left) → Q),
    Q_homomorphism f ∧ set_true_in_alg_model (@f_q_var Γ F hF.left.left f) Γ ∧
    ¬true_in_alg_model (@f_q_var Γ F hF.left.left f) ϕ :=
    @rational_contradicting_valuation Γ ϕ notTrueInLTAlgebra
  obtain ⟨F, hF, f, hf, hΓ', nhϕ'⟩ := h
  have hΓ : set_true_in_alg_model (@f_r_var Γ F hF.left.left f) Γ := by
    intros ψ hψ
    specialize hΓ' ψ hψ
    rw [true_in_alg_model, ←f_r_alg_interpretation (hf := hf), f_r, filter_quot, h_lt]
    rw [true_in_alg_model, ←f_q_alg_interpretation (hf := hf), f_q, filter_quot, h_lt] at hΓ'
    rw [hΓ', incl_top]
  have nhϕ : ¬true_in_alg_model (@f_r_var Γ F hF.left.left f) ϕ := by
    by_contra
    rw [true_in_alg_model, ←f_r_alg_interpretation (hf := hf), f_r, ←incl_top] at this
    rw [true_in_alg_model, ←f_q_alg_interpretation (hf := hf)] at nhϕ'
    exact nhϕ' (incl_inj this)
  exists F, hF, f

theorem completeness_real_unit_interval {Γ : Set Formula} (ϕ : Formula) :
  real_unit_interval_sem_conseq Γ ϕ ↔ Nonempty (Γ ⊢ ϕ) := by
  apply Iff.intro
  · intro unitSemConseq
    by_contra notTrueInLTAlgebra

    have h : ∃ (F : Set (Quotient setoid_formula)) (hF : prime_filter F)
      (f : Quotient setoid_filter → Q),
      set_true_in_alg_model f_r_var Γ ∧
      ¬true_in_alg_model f_r_var ϕ :=
      real_contradicting_valuation ϕ notTrueInLTAlgebra
    obtain ⟨F, hF, f, hΓ, nhϕ⟩ := h

    exact nhϕ (unitSemConseq f_r_var hΓ)
  · exact soundness_real_unit_interval ϕ
