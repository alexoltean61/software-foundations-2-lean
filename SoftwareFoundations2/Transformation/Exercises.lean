import SoftwareFoundations2.Transformation.ConstantFolding

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
      have a₁_simp : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      have a₂_simp : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [a₁_simp, a₂_simp]
      clear a₁_simp a₂_simp
      split
      · rename_i h h'
        rw [h, h']
        simp only [AExp.eval, bne_iff_ne, ne_eq, ite_not]
        split
        · simp only [BExp.eval, bne_eq_false_iff_eq]
          assumption
        · simp only [BExp.eval, bne_iff_ne, ne_eq]
          assumption
      · rw [BExp.eval]
  | BLe a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have a₁_simp : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      have a₂_simp : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [a₁_simp, a₂_simp]
      clear a₁_simp a₂_simp
      split
      · rename_i h h'
        rw [h, h']
        simp only [AExp.eval]
        split
        · rw [BExp.eval, decide_eq_true_eq]
          assumption
        · rw [BExp.eval, decide_eq_false_iff_not]
          assumption
      · rw [BExp.eval]
  | BGt a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have a₁_simp : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      have a₂_simp : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [a₁_simp, a₂_simp]
      clear a₁_simp a₂_simp
      split
      · rename_i h h'
        rw [h, h']
        simp only [AExp.eval]
        split
        · rw [BExp.eval, decide_eq_true_eq]
          assumption
        · rw [BExp.eval, decide_eq_false_iff_not]
          assumption
      · rw [BExp.eval]
  | BNot b ih  =>
      simp only [BExp.eval, BExp.fold_constants]
      split
      · rename_i h
        rw [BExp.eval, Bool.not_eq_eq_eq_not, Bool.not_false, ih, h, BExp.eval]
      · rename_i h
        rw [BExp.eval, Bool.not_eq_eq_eq_not, Bool.not_true, ih, h, BExp.eval]
      · rename_i h h'
        rw [BExp.eval, Bool.not_eq_eq_eq_not, Bool.not_not, ih]
  | BAnd b₁ b₂ ih₁ ih₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      split
      · rename_i h h'
        rw [BExp.eval, Bool.and_eq_true, ih₁, ih₂, h, h', BExp.eval, and_self]
      · rename_i h h'
        rw [ih₁, ih₂, h, h', BExp.eval, BExp.eval, Bool.false_and]
      · rename_i h h'
        rw [ih₁, ih₂, h, h', BExp.eval, Bool.false_and]
      · rename_i h h'
        rw [ih₁, ih₂, h, h', BExp.eval, BExp.eval, Bool.and_false]
      · rw [ih₁, ih₂, BExp.eval]

open ComEval

theorem fold_constants_com_sound : Com.fold_constants.sound := by
  intro c σ₁ σ₂
  induction c generalizing σ₁ σ₂ with
  | CSkip       =>
      rw [Com.fold_constants]
  | CAsgn x a   =>
      apply Iff.intro
      case mp =>
        intros h
        cases h
        case EAsgn eval σσ =>
          apply EAsgn
          · rw [←fold_constants_aexp_sound]
          · rw [σσ, eval]
      case mpr =>
        intros h
        cases h
        case EAsgn eval σσ =>
          rw [←fold_constants_aexp_sound] at eval
          apply EAsgn
          · rfl
          · rw [←eval]
            assumption
  | CSeq c₁ c₂ h₁ h₂  =>
      apply Iff.intro
      · intros h
        cases h
        · rename_i σ' h h'
          rw [h₁] at h
          rw [h₂] at h'
          exact ESeq h h'
      · intros h
        cases h
        · rename_i σ' h h'
          rw [←h₁] at h
          rw [←h₂] at h'
          exact ESeq h h'
  | CIf b c₁ c₂ ih₁ ih₂ =>
      apply Iff.intro
      · intros h
        cases h
        · rename_i bt σσ
          rw [fold_constants_bexp_sound] at bt
          unfold Com.fold_constants
          split
          · assumption
          · rename_i h
            rw [h, BExp.eval] at bt
            contradiction
          · apply EIfTrue bt σσ
        · rename_i bf σσ
          rw [fold_constants_bexp_sound] at bf
          unfold Com.fold_constants
          split
          · rename_i h
            rw [h, BExp.eval] at bf
            contradiction
          · assumption
          · apply EIfFalse bf σσ
      · intros h
        rw [Com.fold_constants] at h
        split at h
        · rename_i h'
          apply EIfTrue
          · rw [fold_constants_bexp_sound, h', BExp.eval]
          · assumption
        · rename_i h'
          apply EIfFalse
          · rw [fold_constants_bexp_sound, h', BExp.eval]
          · assumption
        · cases h
          · apply EIfTrue
            · rename_i h _
              rw [fold_constants_bexp_sound, h]
            · assumption
          · apply EIfFalse
            · rename_i h _
              rw [fold_constants_bexp_sound, h]
            · assumption
  | CWhile b c  =>
      apply Iff.intro
      · intros h
        unfold Com.fold_constants
        split
        · rename_i bt
          rw [←PgmEquiv.true_while]
          · exact h
          · rw [PgmEquiv.bequiv]
            intros σ
            rw [BExp.eval, fold_constants_bexp_sound, bt, BExp.eval]
        · rename_i bf
          cases h
          · apply ESkip
          · rename_i h _ _
            rw [fold_constants_bexp_sound, bf, BExp.eval] at h
            contradiction
        · generalize W : ⟨{ while ↑b do ↑c od }⟩ = loop
          rw [W] at h
          induction h with
          | EWhileFalse bf =>
            simp only [Com.CWhile.injEq] at W
            apply EWhileFalse
            · rw [← fold_constants_bexp_sound, And.left W, bf]
          | EWhileTrue =>
            rename_i bt _ _ _ h
            specialize h W
            simp only [Com.CWhile.injEq] at W
            rw [And.left W]
            rw [And.left W] at h
            apply EWhileTrue
            · rw [←fold_constants_bexp_sound]
              assumption
            · rw [And.right W]
              assumption
            · assumption
          | _ => aesop
      · generalize W : Com.fold_constants ⟨{ while ↑b do ↑c od }⟩ = loop
        unfold Com.fold_constants at W
        split at W
        · intros h
          rw [←W] at h
          rw [PgmEquiv.true_while]
          · assumption
          · rw [PgmEquiv.bequiv]
            intros σ
            rename_i h'
            rw [fold_constants_bexp_sound, h']
        · intros h
          rw [←W] at h
          cases h
          apply EWhileFalse
          rename_i h'
          rw [fold_constants_bexp_sound, h', BExp.eval]
        · intros h
          induction h with
          | EWhileTrue =>
            rename_i bt _ _ _ h
            specialize h W
            simp only [Com.CWhile.injEq] at W
            apply EWhileTrue
            · rw [fold_constants_bexp_sound, And.left W, bt]
            · rw [And.right W]
              assumption
            · assumption
          | EWhileFalse =>
            simp only [Com.CWhile.injEq] at W
            apply EWhileFalse
            rw [fold_constants_bexp_sound, And.left W]
            assumption
          | _ =>
            aesop
