import CertIMP.Transformation.ConstantFolding

open PgmEquiv
open ComEval


theorem fold_constants_aexp_sound : AExp.fold_constants.sound := by
  intro aexp σ
  induction aexp with
  | ANum n      => rfl
  | AId x       => rfl
  | _ =>
      simp only [AExp.eval, *, AExp.fold_constants]
      split
      · next eq1 eq2 =>
          rw [eq1, eq2]
          rfl
      · next => rfl

theorem fold_constants_bexp_sound : BExp.fold_constants.sound := by
  intro bexp σ
  induction bexp with
  | BTrue      => rfl
  | BFalse     => rfl
  | BEq a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      rw [this]; clear this
      have : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [this]; clear this
      split <;> aesop
  | BNeq a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      rw [this]; clear this
      have : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [this]; clear this
      split <;> aesop
  | BLe a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      rw [this]; clear this
      have : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [this]; clear this
      split <;> aesop
  | BGt a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      rw [this]; clear this
      have : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [this]; clear this
      split <;> aesop
  | BNot b ih  =>
      simp only [BExp.eval, BExp.fold_constants]
      rw [ih]
      split <;> aesop
  | BAnd b₁ b₂ ih₁ ih₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      rw [ih₁, ih₂]
      split <;> aesop

theorem fold_constants_com_sound : Com.fold_constants.sound := by
  intro c σ₁ σ₂
  induction c generalizing σ₁ σ₂ with
  | CSkip       =>
      apply Iff.intro
      case CSkip.mp =>
        intro h
        unfold Com.fold_constants
        exact h
      case CSkip.mpr =>
        intro h
        unfold Com.fold_constants at h
        exact h
  | CAsgn x a   =>
      apply Iff.intro <;>
      · intro h
        apply EAsgn rfl
        first | rw [←fold_constants_aexp_sound] | rw [fold_constants_aexp_sound]
        cases h
        · next eq _ =>
          subst eq
          assumption
  | CSeq c₁ c₂ h₁ h₂  =>
      simp only [Com.fold_constants]
      apply Iff.intro <;>
      · intro h
        cases h with
        | ESeq h₃ h₄ =>
          first | rw [h₂] at h₄ ; rw [h₁] at h₃ | rw [←h₂] at h₄ ; rw [←h₁] at h₃
          apply ESeq h₃ h₄
  | CIf b c₁ c₂ =>
      apply Iff.intro
      · intro h
        cases h with
        | EIfTrue heq h =>
            rw [fold_constants_bexp_sound] at heq
            unfold Com.fold_constants
            split
            · assumption
            · next habs => simp [habs] at heq
            · apply EIfTrue heq h
        | EIfFalse heq h =>
            rw [fold_constants_bexp_sound] at heq
            unfold Com.fold_constants
            split
            · next habs => simp [habs] at heq
            · assumption
            · apply EIfFalse heq h
      · intro h
        unfold Com.fold_constants at h
        split at h
        · next heq =>
          apply EIfTrue _ h
          rw [fold_constants_bexp_sound, heq, BExp.eval]
        · next heq =>
          apply EIfFalse _ h
          rw [fold_constants_bexp_sound, heq, BExp.eval]
        · cases h
          · apply EIfTrue _ (by assumption)
            rw [fold_constants_bexp_sound] ; assumption
          · apply EIfFalse _ (by assumption)
            rw [fold_constants_bexp_sound] ; assumption
  | CWhile b c ih  =>
      -- FILL IN HERE
      -- (hint: think about the lemmas you proved previously about `while` commands)
      -- different (and much shorter) structure: the guard folds to `b.fold_constants`,
      -- and `b ≃ b.fold_constants`, so each branch is exactly one of our `while` lemmas.
      have hb := fold_constants_bexp_sound b
      unfold Com.fold_constants
      cases hbf : b.fold_constants with
      | BTrue  => rw [hbf] at hb; exact true_while hb _ _
      | BFalse => rw [hbf] at hb; exact false_while hb _ _
      | _      => rw [hbf] at hb; exact bequiv_congr_while hb _ _
/-


-/
