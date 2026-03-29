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
