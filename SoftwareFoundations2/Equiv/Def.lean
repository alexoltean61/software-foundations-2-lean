import SoftwareFoundations2.Eval

@[simp]
def aequiv (a₁ a₂ : AExp) : Prop :=
  ∀ σ : State, a₁.eval σ = a₂.eval σ

@[simp]
def bequiv (b₁ b₂ : BExp) : Prop :=
  ∀ σ : State, b₁.eval σ = b₂.eval σ

@[simp]
def cequiv (c₁ c₂ : Com) : Prop :=
  ∀ σ σ' : State, σ =[ c₁ ]=> σ' ↔ σ =[ c₂ ]=> σ'

infix:100 " ≃ " => aequiv
infix:100 " ≃ " => bequiv
infix:100 " ≃ " => cequiv
