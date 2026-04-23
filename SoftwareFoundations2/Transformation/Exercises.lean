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

set_option warn.sorry false in
theorem fold_constants_bexp_sound : BExp.fold_constants.sound := by
  intro bexp σ
  induction bexp with
  | BTrue      => rfl
  | BFalse     => rfl
  | BEq a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants, beq_iff_eq]
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

open ComEval

set_option warn.sorry false in
theorem fold_constants_com_sound : Com.fold_constants.sound := by
  intro c σ₁ σ₂
  induction c generalizing σ₁ σ₂ with
  | CSkip       =>
      simp only [Com.fold_constants]
  | CAsgn x a   =>
    simp only [Com.fold_constants]
    apply Iff.intro
    · -- x = a₁ -> x = a₂
        intro h1
        cases h1 with
        | EAsgn eqn eqs =>
            -- Guarantee that 'a' folds safely
            have h_eq := fold_constants_aexp_sound a σ₁
            -- Swap 'a' for 'a.fold_constants' in the evaluation proof
            rw [h_eq] at eqn

            apply EAsgn
            · exact eqn -- updated evaluation proof
            · exact eqs -- untouched state update proof
    · -- x = a₂ -> x = a₁
        intro h2
        cases h2 with
        | EAsgn eqn eqs =>
            have h_eq := fold_constants_aexp_sound a σ₁
            -- Rewrite backwards₁
            rw [← h_eq] at eqn

            apply EAsgn
            · exact eqn
            · exact eqs
  | CSeq c₁ c₂ h₁ h₂  =>
      simp only [Com.fold_constants]
      apply Iff.intro
      · intro hseq
        cases hseq with
        | ESeq hc1 hc2 =>
            -- Build the new sequence
            apply ESeq
            · exact (h₁ _ _).mp hc1
            · exact (h₂ _ _).mp hc2

      · intro hseq
        cases hseq with
        | ESeq hc1 hc2 =>
            apply ESeq
            · exact (h₁ _ _).mpr hc1
            · exact (h₂ _ _).mpr hc2
  | CIf b c₁ c₂ ih₁ ih₂ =>
      -- FILL IN HERE (optional: PR will pass without it)
      sorry
  | CWhile b c  =>
      -- FILL IN HERE (optional: PR will pass without it)
      sorry
