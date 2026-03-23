import GoedelLogic.RationalUnitIntervalCompleteness
import GoedelLogic.RealUnitIntervalSoundness
import Mathlib.Data.Rat.Cast.Order

variable {α : Type} [LAlgebra α]
variable {Γ : Set Formula}
variable {F : Set (Quotient (@setoid_formula Γ))}

theorem qmemR (q : Q) : (q : ℝ) ∈ R := by
  have h : (q : ℚ) ∈ Q := by simp
  apply And.intro
  · exact_mod_cast h.left -- https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#norm_cast
  · exact_mod_cast h.right

def Rhomomorphism (f : Q → R) : Prop :=
                f Top.top = Top.top ∧
                f Bot.bot = Bot.bot ∧
                ∀ (a b : Q), (a ≤ b → f a ≤ f b) ∧
                f (a ⊓ b) = f a ⊓ f b ∧
                f (a ⊔ b) = f a ⊔ f b ∧
                f (a ⇨ b) = f a ⇨ f b

-- The inclusion map Q → R
noncomputable def incl (q : Q) : R := ⟨Rat.castOrderEmbedding q, qmemR q⟩

lemma zeroEqZero :
  ((⟨0, zero_memQ⟩ : Q) : ℝ) = ((⟨0, zero_memR⟩ : R) : ℝ) := by
  simp only [Rat.cast_zero]

lemma oneEqOne :
  ((⟨1, one_memQ⟩ : Q) : ℝ) = ((⟨1, one_memR⟩ : R) : ℝ) := by
  simp only [Rat.cast_one]

lemma inclTop : incl Top.top = Top.top := by
  unfold incl
  apply Subtype.ext
  simp only
  exact oneEqOne

lemma inclBot : incl Bot.bot = Bot.bot := by
  unfold incl
  apply Subtype.ext
  simp only
  exact zeroEqZero

lemma inclOrder : ∀ (a b : Q), (a ≤ b → incl a ≤ incl b) := by
  intro a b hab
  unfold incl
  simp only [Rat.castOrderEmbedding_apply, Subtype.mk_le_mk, Rat.cast_le, Subtype.coe_le_coe]
  exact hab

lemma inclInf : ∀ (a b : Q), incl (a ⊓ b) = incl a ⊓ incl b := by
  intro a b
  unfold incl
  simp [min, SemilatticeInf.inf, Lattice.inf]

lemma inclSup : ∀ (a b : Q), incl (a ⊔ b) = incl a ⊔ incl b := by
  intro a b
  unfold incl
  simp [max, SemilatticeSup.sup]

lemma inclTo : ∀ (a b : Q), incl (a ⇨ b) = incl a ⇨ incl b := by
  intro a b
  unfold incl
  simp [himp, himpQ, himpR]
  split_ifs
  · simp
  · simp

lemma inclinj : Function.Injective incl := by
  intro a b h
  unfold incl at h
  simp only [Subtype.mk.injEq] at h
  apply Subtype.ext
  simp at h
  exact h

-- Define the valuation into R that allows us to prove completeness
noncomputable def f_r_var {hF : filter F} {f : Quotient (@setoid_filter (Quotient setoid_formula) _ _ _) → Q} (v : Var) :=
  incl (f (@filter_quot_var _ _ hF v))

noncomputable def f_r {hF : filter F} {f : Quotient (@setoid_filter (Quotient setoid_formula) _ _ _) → Q} (ϕ : Formula) :=
  incl (f (@filter_quot _ _ hF ϕ))

lemma f_r_alg_interpretation {hF : filter F} {f : Quotient (@setoid_filter (Quotient setoid_formula) _ _ _) → Q} {hf : Qhomomorphism f}:
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
        exact inclBot
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
        exact inclInf (f_q ψ) (f_q χ)
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
        exact inclSup (f_q ψ) (f_q χ)
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
        exact inclTo (f_q ψ) (f_q χ)

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
    Qhomomorphism f ∧ set_true_in_alg_model (@f_q_var Γ F hF.left.left f) Γ ∧
    ¬true_in_alg_model (@f_q_var Γ F hF.left.left f) ϕ :=
    @rational_contradicting_valuation Γ ϕ notTrueInLTAlgebra
  obtain ⟨F, hF, f, hf, hΓ', nhϕ'⟩ := h
  have hΓ : set_true_in_alg_model (@f_r_var Γ F hF.left.left f) Γ := by
    intros ψ hψ
    specialize hΓ' ψ hψ
    rw [true_in_alg_model, ←f_r_alg_interpretation (hf := hf), f_r, filter_quot, h_lt]
    rw [true_in_alg_model, ←f_q_alg_interpretation (hf := hf), f_q, filter_quot, h_lt] at hΓ'
    rw [hΓ', inclTop]
  have nhϕ : ¬true_in_alg_model (@f_r_var Γ F hF.left.left f) ϕ := by
    by_contra
    rw [true_in_alg_model, ←f_r_alg_interpretation (hf := hf), f_r, ←inclTop] at this
    rw [true_in_alg_model, ←f_q_alg_interpretation (hf := hf)] at nhϕ'
    exact nhϕ' (inclinj this)
  exists F, hF, f

theorem completeness_real_unit_interval {Γ : Set Formula} (ϕ : Formula) :
  real_unit_interval_sem_conseq Γ ϕ ↔ Nonempty (Γ ⊢ ϕ) := by
  apply Iff.intro
  · contrapose
    intro notTrueInLTAlgebra
    have h : ∃ (F : Set (Quotient (@setoid_formula Γ))) (hF : prime_filter F)
      (f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ F hF.left.left) → Q),
      set_true_in_alg_model (@f_r_var Γ F hF.left.left f) Γ ∧
      ¬true_in_alg_model (@f_r_var Γ F hF.left.left f) ϕ :=
      @real_contradicting_valuation Γ ϕ notTrueInLTAlgebra
    obtain ⟨F, hF, f, hΓ, nhϕ⟩ := h
    by_contra unitSemCon
    specialize unitSemCon (@f_r_var Γ F hF.left.left f)
    have hϕ : true_in_alg_model (@f_r_var Γ F hF.left.left f) ϕ := by
      apply unitSemCon
      exact hΓ
    exact nhϕ hϕ
  · exact soundness_real_unit_interval ϕ
