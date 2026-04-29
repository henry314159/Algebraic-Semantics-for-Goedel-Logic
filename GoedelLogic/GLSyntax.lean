-- Adapted from: https://github.com/DafinaTrufas/Intuitionistic-Logic-Lean
-- Author: Dafina Trufaș

-- Changed imports for new Mathlib version
import GoedelLogic.Formula
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

-- Added linearity
inductive Proof (Γ : Set Formula) : Formula → Type where
| premise {ϕ} : ϕ ∈ Γ → Proof Γ ϕ
| contractionDisj {ϕ} : Proof Γ (ϕ ∨∨ ϕ ⇒ ϕ)
| contractionConj {ϕ} : Proof Γ (ϕ ⇒ ϕ ∧∧ ϕ)
| weakeningDisj {ϕ ψ} : Proof Γ (ϕ ⇒ ϕ ∨∨ ψ)
| weakeningConj {ϕ ψ} : Proof Γ (ϕ ∧∧ ψ ⇒ ϕ)
| permutationDisj {ϕ ψ} : Proof Γ (ϕ ∨∨ ψ ⇒ ψ ∨∨ ϕ)
| permutationConj {ϕ ψ} : Proof Γ (ϕ ∧∧ ψ ⇒ ψ ∧∧ ϕ)
| exfalso {ϕ} : Proof Γ (⊥ ⇒ ϕ)
| linearity {ϕ ψ} : Proof Γ ((ϕ ⇒ ψ) ∨∨ (ψ ⇒ ϕ))
| modusPonens {ϕ ψ} : Proof Γ ϕ → Proof Γ (ϕ ⇒ ψ) → Proof Γ ψ
| syllogism {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) → Proof Γ (ψ ⇒ χ) → Proof Γ (ϕ ⇒ χ)
| exportation {ϕ ψ χ} : Proof Γ (ϕ ∧∧ ψ ⇒ χ) → Proof Γ (ϕ ⇒ ψ ⇒ χ)
| importation {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ ⇒ χ) → Proof Γ (ϕ ∧∧ ψ ⇒ χ)
| expansion {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) → Proof Γ (χ ∨∨ ϕ ⇒ χ ∨∨ ψ)

infix:25 " ⊢ " => Proof

variable {Γ Δ : Set Formula} {ϕ ψ χ γ : Formula}

namespace Proof

def disjIntroRight : Γ ⊢ ψ ⇒ ϕ ∨∨ ψ := syllogism weakeningDisj permutationDisj

def conjElimRight : Γ ⊢ ϕ ∧∧ ψ ⇒ ψ := syllogism permutationConj weakeningConj

def implProjLeft : Γ ⊢ ϕ ⇒ (ψ ⇒ ϕ) := exportation weakeningConj

def disjOfAndElimLeft : Γ ⊢ ϕ ∧∧ ψ ⇒ ϕ ∨∨ γ := syllogism weakeningConj weakeningDisj

def implSelf : Γ ⊢ ϕ ⇒ ϕ := syllogism contractionConj weakeningConj

def conjIntro : Γ ⊢ ϕ ⇒ ψ ⇒ ϕ ∧∧ ψ := exportation implSelf

def modusPonensAndTh1 : Γ ⊢ (ϕ ⇒ ψ) ∧∧ ϕ ⇒ ψ := importation implSelf

def modusPonensAndTh2 : Γ ⊢ ϕ ∧∧ (ϕ ⇒ ψ) ⇒ ψ := syllogism permutationConj modusPonensAndTh1

def andElimLeftLeft : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ := syllogism weakeningConj weakeningConj

def andElimLeftRight : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ψ := syllogism weakeningConj conjElimRight

def andElimRightLeft : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ ψ := syllogism conjElimRight weakeningConj

def andElimRightRight : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ χ := syllogism conjElimRight conjElimRight

def conjIntroRule : Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ ∧∧ ψ :=
  fun p1 p2 => modusPonens p2 (modusPonens p1 conjIntro)

def conjIntroRule' : Γ ⊢ ϕ ∧∧ ψ → Nonempty (Γ ⊢ ϕ) ∧ Nonempty (Γ ⊢ ψ) :=
  fun p => And.intro (Nonempty.intro (modusPonens p weakeningConj)) ((Nonempty.intro (modusPonens p conjElimRight)))

def conjImplIntroRule : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ χ → Γ ⊢ ϕ ⇒ ψ ∧∧ χ := fun p1 p2 =>
  syllogism contractionConj (importation (syllogism p2 (exportation (syllogism permutationConj
                                                    (importation (syllogism p1 conjIntro))))))

def extraPremise : Γ ⊢ ϕ → Γ ⊢ ψ ⇒ ϕ := fun p => modusPonens p implProjLeft

def andAssoc1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ ∧∧ (ψ ∧∧ χ) :=
  conjImplIntroRule andElimLeftLeft (conjImplIntroRule andElimLeftRight conjElimRight)

def andAssoc2 : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ (ϕ ∧∧ ψ) ∧∧ χ :=
  conjImplIntroRule (conjImplIntroRule weakeningConj andElimRightLeft) andElimRightRight

def extraPremiseConjIntroLeft1 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ∧∧ χ ⇒ ψ := fun p =>
  syllogism weakeningConj p

def extraPremiseConjIntroLeft2 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ χ ∧∧ ϕ ⇒ ψ := fun p =>
  syllogism conjElimRight p

def conjImplComm : Γ ⊢ ϕ ∧∧ ψ ⇒ χ → Γ ⊢ ψ ∧∧ ϕ ⇒ χ := fun p =>
  syllogism permutationConj p

def importationComm : Γ ⊢ ϕ ⇒ ψ ⇒ χ → Γ ⊢ ψ ∧∧ ϕ ⇒ χ := fun p =>
  conjImplComm (importation p)

def extraPremiseConjIntroRight1 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ ϕ ∧∧ ψ := fun p =>
  conjImplIntroRule implSelf p

def andImplDistrib : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ χ ⇒ γ → Γ ⊢ ϕ ∧∧ χ ⇒ ψ ∧∧ γ := fun p1 p2 =>
  conjImplIntroRule (extraPremiseConjIntroLeft1 p1) (extraPremiseConjIntroLeft2 p2)

def permuteHyps : Γ ⊢ ϕ ⇒ ψ ⇒ χ → Γ ⊢ ψ ⇒ ϕ ⇒ χ := fun p => exportation (importationComm p)

def modusPonensExtraHyp : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ ψ ⇒ χ → Γ ⊢ ϕ ⇒ χ := fun p1 p2 =>
  syllogism (extraPremiseConjIntroRight1 p1) (importation p2)

def implExtraHypRev : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ (ψ ⇒ χ) ⇒ (ϕ ⇒ χ) := fun p =>
  exportation (conjImplComm (syllogism (andImplDistrib p implSelf) modusPonensAndTh2))

def implConclTrans : Γ ⊢ ϕ ⇒ (ψ ⇒ χ) → Γ ⊢ χ ⇒ γ → Γ ⊢ ϕ ⇒ (ψ ⇒ γ) := fun p1 p2 =>
  exportation (syllogism (importation p1) p2)

def implOrExtraHyp : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ∨∨ χ ⇒ ψ ∨∨ χ := fun p =>
  syllogism (syllogism permutationDisj (expansion p)) permutationDisj

def extraPremiseDisjIntro1 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ∨∨ ψ ⇒ ψ := fun p =>
  syllogism (implOrExtraHyp p) contractionDisj

def disjIntroAtHyp : Γ ⊢ ϕ ⇒ χ → Γ ⊢ ψ ⇒ χ → Γ ⊢ ϕ ∨∨ ψ ⇒ χ := fun p1 p2 =>
  syllogism (expansion p2) (extraPremiseDisjIntro1 p1)

def orImplDistrib : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ χ ⇒ γ → Γ ⊢ ϕ ∨∨ χ ⇒ ψ ∨∨ γ := fun p1 p2 =>
  disjIntroAtHyp (syllogism p1 weakeningDisj) (syllogism p2 disjIntroRight)

def modusPonensExtraHypTh1 : Γ ⊢ ((ϕ ⇒ (ψ ⇒ χ)) ∧∧ (ϕ ⇒ ψ)) ∧∧ ϕ ⇒ χ :=
  modusPonensExtraHyp (modusPonensExtraHyp conjElimRight andElimLeftRight) (modusPonensExtraHyp conjElimRight andElimLeftLeft)

def implDistrib1 : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇒ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) :=
  exportation (exportation modusPonensExtraHypTh1)

def extraPremiseConjTh : Γ ⊢ (ϕ ∧∧ (ϕ ⇒ ψ) ⇒ χ) ⇒ ϕ ∧∧ ψ ⇒ χ :=
  implExtraHypRev (andImplDistrib implSelf implProjLeft)

def implDistribRule1 : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) → Γ ⊢ ϕ ⇒ ψ ⇒ χ := fun p =>
  exportation (modusPonens (conjImplComm (importation p)) extraPremiseConjTh)

def syllogism_th : Γ ⊢ ϕ ⇒ (ψ ⇒ χ) → Γ ⊢ ϕ ⇒ (χ ⇒ γ) → Γ ⊢ ϕ ⇒ (ψ ⇒ γ) := fun p1 p2 =>
  implDistribRule1 (syllogism (modusPonens p1 implDistrib1) (modusPonens p2 implDistrib1))

def equivDistrib : Γ ⊢ ψ ⇒ ϕ → Γ ⊢ χ ⇒ γ → Γ ⊢ (ϕ ⇒ χ) ⇒ (ψ ⇒ γ) := fun p1 p2 =>
  exportation (modusPonensExtraHyp (modusPonensExtraHyp conjElimRight
  (syllogism_th (extraPremise p1) weakeningConj)) (extraPremise p2))

def exp_extra_hyp : Γ ⊢ ϕ ⇒ (ψ ∧∧ χ ⇒ γ) → Γ ⊢ ϕ ⇒ (ψ ⇒ (χ ⇒ γ)) := fun p =>
  exportation (exportation (syllogism andAssoc1 (importation p)))

def imp_extra_hyp : Γ ⊢ ϕ ⇒ (ψ ⇒ (χ ⇒ γ)) → Γ ⊢ ϕ ⇒ (ψ ∧∧ χ ⇒ γ) := fun p =>
  exportation (syllogism andAssoc2 (importation (importation p)))

noncomputable instance {ϕ : Formula} {Γ : Set Formula} : Decidable (ϕ ∈ Γ) := @default _ (Classical.decidableInhabited _)

-- Added linearity
noncomputable def deductionTheorem_left {ϕ ψ : Formula} (p : Γ ∪ {ϕ} ⊢ ψ) : Γ ⊢ ϕ ⇒ ψ :=
  match p with
  | premise Hvp =>
    if Hvpin : ψ ∈ Γ then extraPremise (premise Hvpin)
    else
      have Heq : ψ = ϕ :=
      by
        cases Hvp
        · contradiction
        · assumption
      by rw [Heq]
         exact implSelf
  | contractionDisj => extraPremise contractionDisj
  | contractionConj => extraPremise contractionConj
  | weakeningDisj => extraPremise weakeningDisj
  | weakeningConj => extraPremise weakeningConj
  | permutationDisj => extraPremise permutationDisj
  | permutationConj => extraPremise permutationConj
  | exfalso => extraPremise exfalso
  | linearity => extraPremise linearity
  | modusPonens p1 p2 => modusPonensExtraHyp (deductionTheorem_left p1) (deductionTheorem_left p2)
  | syllogism p1 p2 => syllogism_th (deductionTheorem_left p1) (deductionTheorem_left p2)
  | importation p => imp_extra_hyp (deductionTheorem_left p)
  | exportation p => exp_extra_hyp (deductionTheorem_left p)
  | expansion p =>
    permuteHyps (disjIntroAtHyp (exportation disjOfAndElimLeft)
                (implConclTrans (permuteHyps (deductionTheorem_left p)) disjIntroRight))

end Proof
