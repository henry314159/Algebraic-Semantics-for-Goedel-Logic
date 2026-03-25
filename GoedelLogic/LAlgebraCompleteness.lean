-- Primarily Trufas' work, with some changes to the proofs, and
-- changes to make it apply to Goedel logic

import GoedelLogic.LAlgebraSoundness

variable {α : Type} [LAlgebra α]
variable {Γ : Set Formula}

-- Define the equivalence relation used to construct the Lindenbaum-Tarski algebra
def equiv (ϕ ψ : Formula) := Nonempty (Γ ⊢ ϕ ⇔ ψ)
infix:50 "∼" => equiv

lemma equiv_and (ϕ ψ : Formula) : @equiv Γ ϕ ψ ↔ Nonempty (Γ ⊢ ϕ ⇒ ψ) ∧ Nonempty (Γ ⊢ ψ ⇒ ϕ) :=
  by
    unfold equiv
    apply Iff.intro
    · intro Hequiv
      apply Proof.conjIntroRule' (Classical.choice Hequiv)
    · intro Hand
      apply Nonempty.intro
      apply Proof.conjIntroRule (Classical.choice Hand.left) (Classical.choice Hand.right)

-- Prove that the relation is indeed an equivalence relation
instance setoid_formula : Setoid Formula :=
  { r := @equiv Γ,
    iseqv := ⟨λ _ => by
                rw [equiv_and]
                exact And.intro (Nonempty.intro Proof.implSelf) (Nonempty.intro Proof.implSelf),
              λ H12 => by
                rw [equiv_and, And.comm]
                rw [equiv_and] at H12
                exact H12,
              λ H12 H23 => by
                rw [equiv_and]
                rw [equiv_and] at H12
                rw [equiv_and] at H23
                apply And.intro
                · apply Nonempty.intro
                  exact Proof.syllogism (Classical.choice H12.left) (Classical.choice H23.left)
                · apply Nonempty.intro
                  exact Proof.syllogism (Classical.choice H23.right) (Classical.choice H12.right)⟩ }

-- Define an order on the Formulas
def Formula.le (ϕ ψ : Formula) : Prop := Nonempty (Γ ⊢ ϕ ⇒ ψ)

-- If ϕ ∼ ϕ' and ψ ∼ ψ', then ϕ ≤ ψ iff ϕ' ≤ ψ'
lemma le_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : @equiv Γ ϕ ϕ' → @equiv Γ ψ ψ' → (@Formula.le Γ ϕ ψ = @Formula.le Γ ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    rw [eq_iff_iff]
    apply Iff.intro
    · intro Hvppsi
      apply Nonempty.intro
      rw [equiv_and] at Heqvp; rw [equiv_and] at Heqpsi
      exact Proof.syllogism (Proof.syllogism (Classical.choice Heqvp.right) (Classical.choice Hvppsi))
                            (Classical.choice Heqpsi.left)
    · intro Hvp'psi'
      apply Nonempty.intro
      rw [equiv_and] at Heqvp; rw [equiv_and] at Heqpsi
      exact Proof.syllogism (Proof.syllogism (Classical.choice Heqvp.left) (Classical.choice Hvp'psi'))
                            (Classical.choice Heqpsi.right)

-- Define the induced order on the Quotient
def le_lt (ϕ ψ : Quotient (@setoid_formula Γ)) : Prop :=
  Quotient.lift₂ (s₁ := @setoid_formula Γ) (s₂ := @setoid_formula Γ) Formula.le le_preserves_equiv ϕ ψ

infix:50 "≤" => le_lt

-- Repeat for or, and, himp
def Formula.or_quot (ϕ ψ : Formula) := Quotient.mk (@setoid_formula Γ) (ϕ ∨∨ ψ)

lemma or_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : @equiv Γ ϕ ϕ' → @equiv Γ ψ ψ' →
  (@Formula.or_quot Γ ϕ ψ = @Formula.or_quot Γ ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    apply Quotient.sound
    rw [equiv_and] at Heqvp
    rw [equiv_and] at Heqpsi
    simp only [HasEquiv.Equiv, Setoid.r, equiv_and]
    apply And.intro
    · apply Nonempty.intro
      exact Proof.orImplDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.orImplDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.right)

def or_lt (ϕ ψ : Quotient (@setoid_formula Γ)) : Quotient (@setoid_formula Γ) :=
  Quotient.lift₂ (s₁ := @setoid_formula Γ) (s₂ := @setoid_formula Γ) Formula.or_quot or_quot_preserves_equiv ϕ ψ

def Formula.and_quot (ϕ ψ : Formula) := Quotient.mk (@setoid_formula Γ) (ϕ ∧∧ ψ)

lemma and_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : @equiv Γ ϕ ϕ' → @equiv Γ ψ ψ' →
  (@Formula.and_quot Γ ϕ ψ = @Formula.and_quot Γ ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    apply Quotient.sound
    rw [equiv_and] at Heqvp
    rw [equiv_and] at Heqpsi
    simp only [HasEquiv.Equiv, Setoid.r, equiv_and]
    apply And.intro
    · apply Nonempty.intro
      exact Proof.andImplDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.andImplDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.right)

def and_lt (ϕ ψ : Quotient (@setoid_formula Γ)) : Quotient (@setoid_formula Γ) :=
  Quotient.lift₂ (s₁ := @setoid_formula Γ) (s₂ := @setoid_formula Γ) Formula.and_quot and_quot_preserves_equiv ϕ ψ

def Formula.to_quot (ϕ ψ : Formula) := Quotient.mk (@setoid_formula Γ) (ϕ ⇒ ψ)

lemma to_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : @equiv Γ ϕ ϕ' → @equiv Γ ψ ψ' →
  (@Formula.to_quot Γ ϕ ψ = @Formula.to_quot Γ ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    apply Quotient.sound
    rw [equiv_and] at Heqvp
    rw [equiv_and] at Heqpsi
    simp only [HasEquiv.Equiv, Setoid.r, equiv_and]
    apply And.intro
    · apply Nonempty.intro
      exact Proof.equivDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.equivDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.right)

def to_lt (ϕ ψ : Quotient (@setoid_formula Γ)) : Quotient (@setoid_formula Γ):=
  Quotient.lift₂ (s₁ := @setoid_formula Γ) (s₂ := @setoid_formula Γ) Formula.to_quot to_quot_preserves_equiv ϕ ψ

-- The LT algebra has a well-defined order operation
instance : LE (Quotient (@setoid_formula Γ)) :=
  { le := le_lt }

-- The LT algebra is an LAlgebra
instance : LAlgebra (Quotient (@setoid_formula Γ)) :=
  { le_refl := λ q => by
      induction q using Quotient.ind
      apply Nonempty.intro
      exact Proof.implSelf
    le_trans := λ q1 q2 q3 H12 H23 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      induction q3 using Quotient.ind
      apply Nonempty.intro
      exact Proof.syllogism (Classical.choice H12) (Classical.choice H23)
    le_antisymm := λ q1 q2 H12 H21 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      apply Quotient.sound
      simp only [HasEquiv.Equiv, Setoid.r, equiv_and]
      apply And.intro H12 H21
    sup := or_lt
    le_sup_left := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      apply Nonempty.intro
      exact Proof.weakeningDisj
    le_sup_right := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      apply Nonempty.intro
      exact Proof.disjIntroRight
    sup_le := λ q1 q2 q3 H13 H23 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      induction q3 using Quotient.ind
      apply Nonempty.intro
      exact Proof.disjIntroAtHyp (Classical.choice H13) (Classical.choice H23)
    inf := and_lt
    inf_le_left := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      apply Nonempty.intro
      exact Proof.weakeningConj
    inf_le_right := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      apply Nonempty.intro
      exact Proof.conjElimRight
    le_inf := λ q1 q2 q3 H13 H23 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      induction q3 using Quotient.ind
      apply Nonempty.intro
      exact Proof.conjImplIntroRule (Classical.choice H13) (Classical.choice H23)
    top := Quotient.mk setoid_formula Formula.top
    le_top := λ q => by
      induction q using Quotient.ind
      apply Nonempty.intro
      exact Proof.extraPremise Proof.exfalso
    himp := to_lt
    le_himp_iff := λ q1 q2 q3 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      induction q3 using Quotient.ind
      apply Iff.intro
      · intro Hle
        apply Nonempty.intro
        exact Proof.importation (Classical.choice Hle)
      · intro Hle
        apply Nonempty.intro
        exact Proof.exportation (Classical.choice Hle)
    bot := Quotient.mk setoid_formula Formula.bottom
    bot_le := λ q => by
      induction q using Quotient.ind
      apply Nonempty.intro
      exact Proof.exfalso
    compl := λ q => to_lt q (Quotient.mk setoid_formula Formula.bottom)
    himp_bot := by simp
    l_axiom := by
      intro a b
      induction a using Quotient.ind
      induction b using Quotient.ind
      rename_i ϕ ψ
      apply Quotient.sound
      simp only [HasEquiv.Equiv, Setoid.r, equiv_and]
      apply And.intro
      · apply Nonempty.intro
        have h : Γ ∪ {(ϕ ⇒ ψ) ∨∨ (ψ ⇒ ϕ)} ⊢ ⊤ := Proof.exfalso
        exact Proof.deductionTheorem_left h
      · apply Nonempty.intro
        have h : Γ ∪ {⊤} ⊢ (ϕ ⇒ ψ) ∨∨ (ψ ⇒ ϕ) := Proof.linearity
        exact Proof.deductionTheorem_left h }

lemma equiv_top (ϕ : Formula)  :
  Nonempty (Γ ⊢ ϕ) ↔ Quotient.mk (@setoid_formula Γ) ϕ = Top.top :=
  by
    simp only [Top.top]
    apply Iff.intro
    · intro Hnempty
      apply Quotient.sound
      simp [HasEquiv.Equiv, Setoid.r, equiv_and]
      apply And.intro
      · apply Nonempty.intro
        exact Proof.extraPremise Proof.exfalso
      · apply Nonempty.intro
        exact Proof.extraPremise (Classical.choice Hnempty)
    · intro Hequiv
      apply Nonempty.intro
      let Hequiv := Quotient.exact Hequiv
      simp [HasEquiv.Equiv, Setoid.r, equiv_and] at Hequiv
      rcases Hequiv with ⟨_, Hr⟩
      exact Proof.modusPonens Proof.exfalso (Classical.choice Hr)

-- Define the canonical valuation into the LT algebra
def h_lt_var (v : Var) : Quotient (@setoid_formula Γ) := Quotient.mk setoid_formula (Formula.var v)

-- Define the interpretation of Formulas in the LT algebra
def h_lt (ϕ : Formula) : Quotient (@setoid_formula Γ) := Quotient.mk setoid_formula ϕ

-- Prove that h_lt is the extension of h_lt_var in the sense of AlgInterpretation
lemma h_lt_interpretation :
  ∀ (ϕ : Formula),  h_lt ϕ = (@AlgInterpretation (Quotient (@setoid_formula Γ)) _ h_lt_var ϕ) :=
  by
    intro ϕ
    induction ϕ with
    | var v => rfl
    | bottom =>
        unfold h_lt
        unfold AlgInterpretation
        simp only [Bot.bot]
    | and ψ χ ih1 ih2 =>
        have Haux : Quotient.mk (@setoid_formula Γ) (ψ∧∧χ)
        = and_lt (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) := rfl
        rw [h_lt, AlgInterpretation, Haux, <-ih1, <-ih2] -- changed from simp only [Inf.inf]
        rfl
    | or ψ χ ih1 ih2 =>
        have Haux : Quotient.mk (@setoid_formula Γ) (ψ∨∨χ)
        = or_lt (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) := rfl
        rw [h_lt, AlgInterpretation, Haux, <-ih1, <-ih2] -- changed from simp only [Sup.sup]
        rfl
    | implication ψ χ ih1 ih2 =>
        have Haux : Quotient.mk (@setoid_formula Γ) (ψ⇒χ)
        = to_lt (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) := rfl
        rw [h_lt, AlgInterpretation, Haux, <-ih1, <-ih2]
        rfl

-- Show that Γ is true in the algebraic model under the valuation h_lt_var
lemma set_true_in_lt :
  @set_true_in_alg_model (Quotient (@setoid_formula Γ)) _ h_lt_var Γ :=
  by
    intro ϕ Hin
    rw [true_in_alg_model, ← h_lt_interpretation, h_lt, ← equiv_top]
    apply Nonempty.intro
    exact Proof.premise Hin

-- Show that ϕ is true in the algebraic model under h_lt_var iff Γ ⊢ ϕ
lemma true_in_lt (ϕ : Formula) :
  @true_in_alg_model (Quotient (@setoid_formula Γ)) _ h_lt_var ϕ ↔ Nonempty (Γ ⊢ ϕ) :=
  by
    apply Iff.intro
    · intro Htruelt
      apply Nonempty.intro
      rw [true_in_alg_model, ← h_lt_interpretation, h_lt, ← equiv_top] at Htruelt
      exact Classical.choice Htruelt
    · intro Hnempty
      rw [equiv_top] at Hnempty
      rw [true_in_alg_model, ← h_lt_interpretation]
      exact Hnempty

-- The completeness theorem for LAlgebras
theorem completeness_lalg (ϕ : Formula) :
  alg_sem_conseq Γ ϕ ↔ Nonempty (Γ ⊢ ϕ) :=
  by
    apply Iff.intro
    · intro Halg
      rw [← true_in_lt]
      exact Halg (Quotient (@setoid_formula Γ)) h_lt_var set_true_in_lt
    · exact soundness_lalg ϕ
