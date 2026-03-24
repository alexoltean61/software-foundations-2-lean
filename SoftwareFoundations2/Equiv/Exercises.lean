import SoftwareFoundations2.Equiv.Def

open ComEval

variable {c c₁ c₂ c₃ : Com}
variable {b : BExp}

theorem aequiv_example : aexp⟨{ x - x }⟩ ≃ aexp⟨{ 0 }⟩ := by
  simp [aequiv, AExp.eval]

theorem bequiv_example : bexp⟨{ x - x == 0 }⟩ ≃ bexp⟨{ btrue }⟩ := by
  simp [bequiv, BExp.eval]

theorem skip_left : ⟨{ skip; ↑c }⟩ ≃ ⟨{ ↑c }⟩ := by
  -- WORKED IN CLASS
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h with
    | ESeq h1 h2 =>
        cases h1
        exact h2
  · intro h
    apply ESeq ESkip
    exact h

theorem true_if (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ ↑c₁ }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h1
    cases h1 with
    | EIfTrue _ _ => assumption
    | EIfFalse habs _ =>
        simp only [bequiv, BExp.eval] at h
        specialize h σ
        rw [h] at habs
        contradiction
  · intro h1
    apply EIfTrue _ h1
    apply h

theorem false_while (h : b ≃ bexp⟨{ bfalse }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ skip }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h1
    cases h1 with
    | EWhileFalse => exact ESkip
    | EWhileTrue habs =>
        simp only [bequiv, BExp.eval] at h
        specialize h σ
        rw [h] at habs
        contradiction
  · intro h2
    cases h2
    apply EWhileFalse
    apply h

theorem true_while_nonterm
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ¬ σ =[ while ↑b do ↑c od ]=> σ' := by
  -- WORKED IN CLASS
  generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop
  intro habs
  induction habs with
  | EWhileFalse habs =>
      aesop
  | EWhileTrue htrue h1 h2 _ ih =>
      exact ih eq
  | _ => aesop

theorem loop_unrolling :
  ⟨{  while ↑b do ↑c od  }⟩ ≃
  ⟨{  if ↑b then
        ↑c;
        while ↑b do ↑c od;
      else
        skip;
      endif
  }⟩ := by
  -- WORKED IN CLASS
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h with
    | EWhileTrue beval =>
        apply EIfTrue beval
        apply ESeq
        repeat assumption
    | EWhileFalse beval =>
        apply EIfFalse beval
        apply ESkip
  · intro h
    cases h with
    | EIfTrue beval h =>
        cases h
        apply EWhileTrue beval
        repeat assumption
    | EIfFalse beval h =>
        cases h
        apply EWhileFalse beval

theorem identity_assignment :
  ⟨{ x = x }⟩ ≃ ⟨{ skip }⟩ := by
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h
    case EAsgn n eqn eqs
    · subst eqn
      simp only [AExp.eval, State.set_id] at eqs
      subst eqs
      exact ESkip
  · intro h
    cases h
    apply EAsgn rfl
    simp only [AExp.eval, State.set_id]

theorem skip_right : ⟨{ ↑c; skip }⟩ ≃ ⟨{ ↑c }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros h
    cases h
    case ESeq c₁ c₂ =>
      cases c₂
      exact c₁
  case mpr =>
    intros h
    apply ESeq
    · exact h
    · apply ESkip

theorem false_if (h : b ≃ bexp⟨{ bfalse }⟩) :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ ↑c₂ }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros c
    cases c
    case EIfTrue bt cod =>
      unfold bequiv at h
      specialize h σ
      rw [h] at bt
      simp at bt
    case EIfFalse bf cod =>
      exact cod
  case mpr =>
    intros cod
    apply EIfFalse
    · unfold bequiv at h
      specialize h σ
      rw [BExp.eval] at h
      exact h
    · exact cod

theorem swap_if_branches :
    ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃
    ⟨{ if !↑b then ↑c₂ else ↑c₁ endif }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros h
    cases h
    case EIfTrue bt c1 =>
      apply EIfFalse
      · unfold BExp.eval
        rw [bt]
        simp
      · exact c1
    case EIfFalse bf c2 =>
      apply EIfTrue
      · unfold BExp.eval
        rw [bf]
        simp
      · exact c2
  case mpr =>
    intros h
    cases h
    case EIfTrue nbt c2 =>
      apply EIfFalse
      · unfold BExp.eval at nbt
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at nbt
        exact nbt
      · exact c2
    case EIfFalse nbf c1 =>
      apply EIfTrue
      · unfold BExp.eval at nbf
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at nbf
        exact nbf
      · exact c1

theorem true_while
  (h : b ≃ bexp⟨{ btrue }⟩) :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while btrue do skip od }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros h'
    apply true_while_nonterm at h'
    · exact h'.elim
    · exact h
  case mpr =>
    intros h'
    apply true_while_nonterm at h'
    · exact h'.elim
    · simp
  -- Hint: You'll want to use `true_while_nonterm` here.

theorem assign_aequiv
  (h : aexp⟨{ x }⟩ ≃ a ) :
  ⟨{ x = ↑a }⟩ ≃ ⟨{ skip }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros h'
    cases h'
    case EAsgn n neval sigsig' =>
      rw [neval] at sigsig'
      specialize h σ
      rw [← h] at sigsig'
      simp only [AExp.eval, State.set_id] at sigsig'
      rw [sigsig']
      apply ESkip
  case mpr =>
    intros h'
    cases h'
    case ESkip =>
      apply EAsgn
      · rfl
      · specialize h σ
        rw [← h, AExp.eval, State.set_id]

theorem seq_assoc : ⟨{ {↑c₁ ; ↑c₂} ; ↑c₃ }⟩ ≃ ⟨{ ↑c₁ ; {↑c₂ ; ↑c₃} }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros h
    cases h
    case ESeq c12 c3 =>
      cases c12
      case ESeq c1 c2 =>
        exact ESeq c1 (ESeq c2 c3)
  case mpr =>
    intros h
    cases h
    case ESeq c1 c23 =>
      cases c23
      case ESeq c2 c3 =>
        exact ESeq (ESeq c1 c2) c3
  -- FILL IN HERE (optional: PR will pass without it)

@[refl]
theorem equiv_refl : c ≃ c := by
  intros σ σ'
  rfl

@[trans]
theorem equiv_trans : c₁ ≃ c₂ → c₂ ≃ c₃ → c₁ ≃ c₃ := by
  intros c12 c23
  intros σ σ'
  specialize c12 σ σ'
  specialize c23 σ σ'
  rw [c12, c23]

@[symm]
theorem equiv_symm : c₁ ≃ c₂ → c₂ ≃ c₁ := by
  intros h
  intros σ σ'
  specialize h σ σ'
  rw [h]

theorem equiv_congr_asgn {a₁ a₂ : AExp} (h : a₁ ≃ a₂) :
  ⟨{ ↑x = ↑a₁ }⟩ ≃ ⟨{ ↑x = ↑a₂ }⟩ := by
  intros σ σ'
  specialize h σ
  apply Iff.intro
  case mp =>
    intros h'
    apply EAsgn
    · rfl
    · rw [← h]
      cases h'
      case a.EAsgn n n_is_a₁ sigsig' =>
        rw [n_is_a₁] at sigsig'
        exact sigsig'
  case mpr =>
    intros h'
    apply EAsgn
    · rfl
    · rw [h]
      cases h'
      case a.EAsgn n n_is_a₂ sigsig' =>
        rw [n_is_a₂] at sigsig'
        exact sigsig'

theorem equiv_congr_seqL (h : c₁ ≃ c₁') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁'; ↑c₂ }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros c1c2
    cases c1c2
    case ESeq σ'' sigsig'' sig''sig' =>
      rw [h] at sigsig''
      apply ESeq
      · exact sigsig''
      · exact sig''sig'
  case mpr =>
    intros c1'c2
    cases c1'c2
    case ESeq σ'' sigsig'' sig''sig' =>
      rw [←h] at sigsig''
      apply ESeq
      · exact sigsig''
      · exact sig''sig'

theorem equiv_congr_seqR (h : c₂ ≃ c₂') :
  ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁; ↑c₂' }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros h'
    cases h'
    case ESeq σ'' σσ'' σ''σ' =>
      rw [h] at σ''σ'
      apply ESeq
      · assumption
      · assumption
  case mpr =>
    intros h'
    cases h'
    case ESeq σ'' σσ'' σ''σ' =>
      rw [←h] at σ''σ'
      apply ESeq
      · assumption
      · assumption

theorem bequiv_congr_if (h : b ≃ b') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b' then ↑c₁ else ↑c₂ endif }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros h'
    cases h'
    case EIfTrue bt σσ' =>
      rw [h] at bt
      exact EIfTrue bt σσ'
    case EIfFalse bf σσ' =>
      rw [h] at bf
      exact EIfFalse bf σσ'
  case mpr =>
    intros h'
    cases h'
    case EIfTrue bt σσ' =>
      rw [←h] at bt
      exact EIfTrue bt σσ'
    case EIfFalse bf σσ' =>
      rw [←h] at bf
      exact EIfFalse bf σσ'

theorem equiv_congr_if (h₁ : c₁ ≃ c₁') (h₂ : c₂ ≃ c₂') :
  ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ≃ ⟨{ if ↑b then ↑c₁' else ↑c₂' endif }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    intros h
    cases h
    case EIfTrue bt σσ' =>
      apply EIfTrue bt
      rw [h₁] at σσ'
      assumption
    case EIfFalse bf σσ'=>
      apply EIfFalse bf
      rw [h₂] at σσ'
      assumption
  case mpr =>
    intros h
    cases h
    case EIfTrue bt σσ' =>
      apply EIfTrue bt
      rw [←h₁] at σσ'
      assumption
    case EIfFalse bf σσ'=>
      apply EIfFalse bf
      rw [←h₂] at σσ'
      assumption

theorem bequiv_congr_while (h : b ≃ b') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b' do ↑c od }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    -- Credit Liana pentru ca mi-a zis cum sa fac inductie pe tipuri neinductive
    generalize W : ⟨{ while ↑b do ↑c od }⟩ = loop
    intros h'
    induction h' with
    | EWhileFalse bf =>
      simp only [Com.CWhile.injEq] at W
      rcases W with ⟨bb_cross, _⟩
      apply EWhileFalse
      · rw [←h, bb_cross]
        assumption
    | EWhileTrue bt σσ' σ'σ'' h' ih =>
      simp only [Com.CWhile.injEq] at W
      rcases W with ⟨bb_cross, cc_cross⟩
      rw [bb_cross, cc_cross] at ih
      specialize ih rfl
      rw [←bb_cross, h] at bt
      rw [cc_cross]
      apply EWhileTrue bt σσ' ih
    | _ => aesop
  case mpr =>
    generalize W : ⟨{ while ↑b' do ↑c od }⟩ = loop'
    intros h'
    induction h' with
    | EWhileFalse b'f =>
      simp only [Com.CWhile.injEq] at W
      rcases W with ⟨b'b_cross, _⟩
      apply EWhileFalse
      · rw [h, b'b_cross]
        assumption
    | EWhileTrue b't σσ' σ'σ'' h' ih =>
      simp only [Com.CWhile.injEq] at W
      rcases W with ⟨b'b_cross, cc_cross⟩
      rw [b'b_cross, cc_cross] at ih
      specialize ih rfl
      rw [←b'b_cross, ←h] at b't
      rw [cc_cross]
      apply EWhileTrue b't σσ' ih
    | _ => aesop

theorem equiv_congr_while {c c' : Com} (h : c ≃ c') :
  ⟨{ while ↑b do ↑c od }⟩ ≃ ⟨{ while ↑b do ↑c' od }⟩ := by
  intros σ σ'
  apply Iff.intro
  case mp =>
    generalize W : ⟨{ while ↑b do ↑c od }⟩ = loop
    intros h'
    induction h' with
    | EWhileFalse bf =>
      simp only [Com.CWhile.injEq] at W
      rcases W with ⟨bb_cross, cc_cross⟩
      rw [←bb_cross] at bf
      exact EWhileFalse bf
    | EWhileTrue bt σσ' σ'σ'' h' ih =>
      simp only [Com.CWhile.injEq] at W
      rcases W with ⟨bb_cross, cc_cross⟩
      rw [bb_cross, cc_cross] at ih
      specialize ih rfl
      rw [←bb_cross] at ih
      rw [←bb_cross] at bt
      apply EWhileTrue bt _ ih
      · rw [←h, cc_cross]
        assumption
    | _ => aesop
  case mpr =>
    generalize W : ⟨{ while ↑b do ↑c' od }⟩ = loop'
    intros h'
    induction h' with
    | EWhileFalse bf =>
      simp only [Com.CWhile.injEq] at W
      rcases W with ⟨bb_cross, c'c_cross⟩
      rw [←bb_cross] at bf
      exact EWhileFalse bf
    | EWhileTrue bt σσ' σ'σ'' h' ih =>
      simp only [Com.CWhile.injEq] at W
      rcases W with ⟨bb_cross, c'c_cross⟩
      rw [bb_cross, c'c_cross] at ih
      specialize ih rfl
      rw [←bb_cross] at ih
      rw [←bb_cross] at bt
      apply EWhileTrue bt _ ih
      · rw [h, c'c_cross]
        assumption
    | _ => aesop
