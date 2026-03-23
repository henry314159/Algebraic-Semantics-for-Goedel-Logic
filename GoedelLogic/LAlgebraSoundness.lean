-- Primarily Trufas' work, with some changes to the proofs, and to apply to Goedel logic instead

import GoedelLogic.Filters
import GoedelLogic.Formula
import GoedelLogic.GLSyntax

variable {α : Type} [LAlgebra α]

-- Extend the valuation I inductively
def AlgInterpretation (I : Var → α) : Formula → α
| Formula.var p => I p
| Formula.bottom => ⊥
| ϕ ∧∧ ψ => AlgInterpretation I ϕ ⊓ AlgInterpretation I ψ
| ϕ ∨∨ ψ => AlgInterpretation I ϕ ⊔ AlgInterpretation I ψ
| ϕ ⇒ ψ => AlgInterpretation I ϕ ⇨ AlgInterpretation I ψ

lemma alg_compl {ϕ : Formula} (I : Var → α) : AlgInterpretation I (Formula.negation ϕ) = (AlgInterpretation I ϕ)ᶜ :=
  by
    have Haux1 : AlgInterpretation I (ϕ ⇒ ⊥) = AlgInterpretation I ϕ ⇨ AlgInterpretation I ⊥ := rfl
    have Haux2 : AlgInterpretation I ⊥ = Bot.bot := rfl
    simp [Formula.negation, Haux1, Haux2]

lemma alg_top (I : Var → α) : AlgInterpretation I Formula.top = Top.top :=
  by
    have Haux1 : AlgInterpretation I ⊤ = AlgInterpretation I ⊥ ⇨ AlgInterpretation I ⊥ := by rfl
    have Haux2 : AlgInterpretation I ⊥ = Bot.bot := by rfl
    simp only [Haux1, Haux2, himp_self]

-- A Formula ϕ is interpreted as true iff ϕ is sent to ⊤
def true_in_alg_model (I : Var → α) (ϕ : Formula) : Prop := AlgInterpretation I ϕ = Top.top

-- A formula is valid in an algebra if it is true under all possible valuations
def valid_in_alg (ϕ : Formula) : Prop := ∀ (I : Var → α), true_in_alg_model I ϕ

-- A formula is algebraically valid if it is valid in all LAlgebras
def alg_valid (ϕ : Formula) : Prop := ∀ (β : Type) [LAlgebra β], @valid_in_alg β _ ϕ

-- Same definitions for a set of Formulas
def set_true_in_alg_model (I : Var → α) (Γ : Set Formula) : Prop :=
  ∀ (ϕ : Formula), ϕ ∈ Γ → true_in_alg_model I ϕ

def set_valid_in_alg (Γ : Set Formula) : Prop := ∀ (I : Var → α), set_true_in_alg_model I Γ

def set_alg_valid (Γ : Set Formula) : Prop :=
  ∀ (β : Type) [LAlgebra β], @set_valid_in_alg β _ Γ

-- Γ ⊨ ϕ iff Γ is algebraically valid implies ϕ is algebraically valid
def alg_sem_conseq (Γ : Set Formula) (ϕ : Formula) : Prop :=
  ∀ (β : Type) [LAlgebra β] (I : Var → β),
  set_true_in_alg_model I Γ → true_in_alg_model I ϕ

lemma empty_conseq_alg_valid (ϕ : Formula) :
  alg_sem_conseq ∅ ϕ ↔ alg_valid ϕ :=
  by
    apply Iff.intro
    · intro Hconseq _ _ I
      simp [alg_sem_conseq, set_true_in_alg_model] at Hconseq
      exact Hconseq _ I
    · intro Halgvalid _ _ I _
      exact Halgvalid _ I

lemma elem_alg_sem_conseq (Γ : Set Formula) (ϕ : Formula) : ϕ ∈ Γ → alg_sem_conseq Γ ϕ :=
  by
    intro Hin _ _ _ Hsettrue
    exact Hsettrue ϕ Hin

lemma alg_valid_sem_conseq (Γ : Set Formula) (ϕ : Formula) : alg_valid ϕ → alg_sem_conseq Γ ϕ :=
  by
    intro Halgvalid _ _ I _
    exact Halgvalid _ I

-- The class of LAlgebras is sound for Goedel logic
-- added linearity, and changed some proofs
theorem soundness_lalg {Γ : Set Formula} (ϕ : Formula) : Nonempty (Γ ⊢ ϕ) → alg_sem_conseq Γ ϕ :=
  by
    intro Htheorem
    let Htheorem' := Classical.choice Htheorem
    induction Htheorem' with
    | @premise ϕ Hin => intro _ _ _ Hsettrue
                        exact Hsettrue ϕ Hin
    | @contractionDisj ψ => intro _ _ _ _
                            simp [true_in_alg_model, AlgInterpretation]
    | @contractionConj ψ => intro _ _ _ _
                            simp [true_in_alg_model, AlgInterpretation]
    | @weakeningDisj ψ χ => intro _ _ _ _
                            simp [true_in_alg_model, AlgInterpretation]
    | @weakeningConj ψ χ => intro _ _ _ _
                            simp [true_in_alg_model, AlgInterpretation]
    | @permutationDisj ψ χ => intro _ _ _ _
                              simp [true_in_alg_model, AlgInterpretation]
    | @permutationConj ψ χ => intro _ _ _ _
                              simp [true_in_alg_model, AlgInterpretation]
    | @exfalso ψ => intro _ _ _ _
                    simp [true_in_alg_model, AlgInterpretation]
    | @linearity ψ χ => intro _ _ _ _
                        rw [true_in_alg_model, AlgInterpretation]
                        apply LAlgebra.l_axiom
    | @modusPonens ψ χ p1 p2 ih1 ih2 => intro _ _ _ Hsettrue
                                        simp at ih1
                                        simp at ih2
                                        specialize ih1 p1 _ _ Hsettrue
                                        specialize ih2 p2 _ _ Hsettrue
                                        rw [true_in_alg_model, AlgInterpretation, ih1] at ih2
                                        simp at ih2
                                        exact ih2
    | @syllogism ψ χ γ p1 p2 ih1 ih2 => intro _ _ _ Hsettrue
                                        simp at ih1
                                        simp at ih2
                                        specialize ih1 p1 _ _ Hsettrue
                                        specialize ih2 p2 _ _ Hsettrue
                                        rw [true_in_alg_model, AlgInterpretation] at ih1
                                        simp at ih1
                                        rw [true_in_alg_model, AlgInterpretation] at ih2
                                        simp at ih2
                                        rw [true_in_alg_model, AlgInterpretation]
                                        simp
                                        apply le_trans ih1 ih2
    | @exportation ψ χ γ p ih => intro _ _ _ Hsettrue
                                 simp at ih
                                 specialize ih p _ _ Hsettrue
                                 simp [true_in_alg_model, AlgInterpretation] at ih
                                 simp [true_in_alg_model, AlgInterpretation]
                                 exact ih
    | @importation ψ χ γ p ih => intro _ _ _ Hsettrue
                                 simp at ih
                                 specialize ih p _ _ Hsettrue
                                 simp [true_in_alg_model, AlgInterpretation] at ih
                                 simp [true_in_alg_model, AlgInterpretation]
                                 exact ih
    | @expansion ψ χ γ p ih => intro _ _ _ Hsettrue
                               simp at ih
                               specialize ih p _ _ Hsettrue
                               simp [true_in_alg_model, AlgInterpretation] at ih
                               rw [true_in_alg_model, AlgInterpretation, AlgInterpretation, himp_eq_top_iff]
                               apply sup_le_sup_left
                               exact ih
