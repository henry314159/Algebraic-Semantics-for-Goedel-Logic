import GoedelLogic.LAlgebraSoundness

-- Define chain as the property of being a totally ordered LAlgebra
def chain (α : Type) [LAlgebra α] : Prop := ∀ (a b : α), a ≤ b ∨ b ≤ a

-- Define chain semantic consequence
def chain_sem_conseq (Γ : Set Formula) (ϕ : Formula): Prop :=
  ∀ (α : Type) [LAlgebra α] (I : Var → α),
  chain α ∧ set_true_in_alg_model I Γ → true_in_alg_model I ϕ

-- Soundness for chains follows immediately from soundness for LAlgebras,
-- because chains are LAlgebras
theorem soundness_chains {Γ : Set Formula} (ϕ : Formula) : Nonempty (Γ ⊢ ϕ) → chain_sem_conseq Γ ϕ :=
  by
    intro Htheorem
    apply soundness_lalg ϕ at Htheorem
    intro _ _ _ h_ab
    exact Htheorem _ _ h_ab.right



















class Chain (α : Type*) extends LAlgebra α, LinearOrder α

/-instance chain_lalgebra {α : Type*} [Chain α] : LAlgebra α :=
  { l_axiom := by
                 intro a b
                 rw [le_antisymm_iff]
                 apply And.intro
                 · exact le_top
                 · cases le_total a b with
                    | inl h₁ =>
                        rw [<-himp_eq_top_iff] at h₁
                        rw [h₁]
                        exact le_sup_left
                    | inr h₂ =>
                        rw [<-himp_eq_top_iff] at h₂
                        rw [h₂]
                        exact le_sup_right
  }-/

def chain_sem_conseq1 (Γ : Set Formula) (ϕ : Formula) : Prop :=
  ∀ (α : Type) [Chain α] (I : Var → α),
  set_true_in_alg_model I Γ → true_in_alg_model I ϕ

theorem soundness_chains1 (ϕ : Formula) : Nonempty (Γ ⊢ ϕ) → chain_sem_conseq1 Γ ϕ :=
  by
    intro Htheorem
    apply soundness_lalg ϕ at Htheorem
    intro α
    exact Htheorem α
