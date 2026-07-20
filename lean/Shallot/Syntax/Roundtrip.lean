import Shallot.Syntax.RoundtripExpr
import Shallot.Peg.Completeness
import Shallot.Lang.TypeSound
import Shallot.Lang.TypeCheckVerify
import Shallot.Vm.Correct

/-!
# RT-L3 — the PROGRAM layer of the parser roundtrip, and the pipeline theorem

Builds on RT-L2 (`derives_printExpr`, expression layer) to prove that the
canonical text of a whole program parses back — as a `Derives` derivation
(`derives_printProgram`), and through the verified interpreter
(`parse_print`, via completeness T3 + fuel monotonicity T0). The file
closes with `pipeline_correct`, composing print→parse (this file),
typechecking soundness (`checkProgram_sound`), evaluation type soundness
(`runProgram_sound`) and compiler correctness (`compile_correct`).

## The printable-program hypothesis, and the one boundary hazard

`printableProgB` is the printability of all identifiers/bodies PLUS a
separation guard `sepOkB`. The guard is NOT an artifact of the proof — it
excludes the single genuinely-broken printer boundary: when the LAST
function's body is a bare variable and `main`'s canonical text starts with
`'('`, the PEG's prioritized `Call / Ident` choice extends the body across
the boundary (`… = x ( 1 + 2 ) ` parses `x ( 1 + 2 )` as a call, and the
program parse then FAILS at EOF). Checked empirically:
`parseShallot _ "def f ( ) : int = x ( 1 + 2 ) " = .error .syntaxErr`.
Every other boundary is safe, which needs a strengthened expression-layer
lemma: `derives_print_primary_nv` re-derives the RT-L2 core for every
non-`var` shape while ALLOWING a `'('`-headed follow (the `headNot '('`
hypothesis of `derives_print_primary` is used only by its `var` case).
-/

set_option autoImplicit false

namespace Shallot

/-! ## Rule lemmas -/

theorem type'_rule : ruleAt shallotGrammar.rules NT.type' =
    some (.alt (kw "int") (kw "bool")) := rfl

theorem program_rule : ruleAt shallotGrammar.rules NT.program =
    some (.seq (.nt NT.spacing)
      (.seq (.star (.nt NT.funDef)) (.seq (.nt NT.expr) (.notP .any)))) := rfl

theorem funDef_rule : ruleAt shallotGrammar.rules NT.funDef =
    some (.seq (kw "def") (.seq (.nt NT.ident)
      (.seq (tok "(") (.seq (PExp.opt (.nt NT.params))
        (.seq (tok ")") (.seq (tok ":") (.seq (.nt NT.type')
          (.seq eqTok (.nt NT.expr))))))))) := rfl

theorem params_rule : ruleAt shallotGrammar.rules NT.params =
    some (.seq (.nt NT.param) (.star (.seq (tok ",") (.nt NT.param)))) := rfl

theorem param_rule : ruleAt shallotGrammar.rules NT.param =
    some (.seq (.nt NT.ident) (.seq (tok ":") (.nt NT.type'))) := rfl

/-! ## Printable programs -/

/-- The expression is a bare variable (a lone `Ident` at `Primary` level —
the only canonical text a following `'('` can extend, into a `Call`). -/
def bareVarB : Expr → Bool
  | .var _ => true
  | _ => false

/-- `printExpr e` starts with `'('` (compound shapes, and negative
literals, which print as `( - digits ) `). -/
def parenHeadB : Expr → Bool
  | .intLit n => decide (n < 0)
  | .unop _ _ => true
  | .binop _ _ _ => true
  | .ite _ _ _ => true
  | .letE _ _ _ => true
  | _ => false

/-- Printability of one function: valid non-keyword name, valid parameter
names, printable body (parameter types are just `int`/`bool` — always
printable). -/
def printableFunB (d : FunDef) : Bool :=
  validIdentB d.name && d.params.all (fun pr => validIdentB pr.1) && printableB d.body

/-- The separation guard (see the file docstring): the LAST function's
body must not be a bare variable when `main` prints `'('`-headed. This is
the exact condition — every other function is followed by `"def …"`. -/
def sepOkB : List FunDef → Expr → Bool
  | [], _ => true
  | [d], m => !(bareVarB d.body && parenHeadB m)
  | _ :: ds, m => sepOkB ds m

/-- RT-L3 roundtrip hypothesis: all functions printable, `main` printable,
and the boundary guard holds. -/
def printableProgB (p : Program) : Bool :=
  p.funs.all printableFunB && printableB p.main && sepOkB p.funs p.main

/-- Text-level form of the guard, for the `FunDef*` induction: if the last
function's body is a bare variable, the star's follow must not start `'('`. -/
def sepListB : List FunDef → List Char → Bool
  | [], _ => true
  | d :: ds, follow =>
    match ds with
    | [] => !bareVarB d.body || headNot '(' follow
    | _ :: _ => sepListB ds follow

/-! ## The weak follow condition

`opFollowB` is `exprFollowB` MINUS the `'('` exclusion: no operator token
can start at the boundary, but a `'('` may. It is what a non-`var`
expression parse actually needs from its follow text. -/

def opFollowB : List Char → Bool
  | [] => true
  | c :: _ => !(beqChar '+' c || beqChar '-' c || beqChar '*' c || beqChar '/' c ||
      beqChar '%' c || beqChar '<' c || beqChar '=' c || beqChar '&' c ||
      beqChar '|' c)

theorem opFollowB_cons (c : Char) (cs : List Char)
    (h : (beqChar '+' c || beqChar '-' c || beqChar '*' c || beqChar '/' c ||
      beqChar '%' c || beqChar '<' c || beqChar '=' c || beqChar '&' c ||
      beqChar '|' c) = false) : opFollowB (c :: cs) = true := by
  simp only [opFollowB, h, Bool.not_false]

theorem opFollowB_spec (r : List Char) (h : opFollowB r = true) :
    headNot '+' r = true ∧ headNot '-' r = true ∧ headNot '*' r = true ∧
    headNot '/' r = true ∧ headNot '%' r = true ∧ headNot '<' r = true ∧
    headNot '=' r = true ∧ headNot '&' r = true ∧ headNot '|' r = true := by
  cases r with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons c cs =>
    simp only [opFollowB, Bool.not_eq_true', Bool.or_eq_false_iff] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    exact ⟨headNot_cons _ _ _ h1, headNot_cons _ _ _ h2, headNot_cons _ _ _ h3,
      headNot_cons _ _ _ h4, headNot_cons _ _ _ h5, headNot_cons _ _ _ h6,
      headNot_cons _ _ _ h7, headNot_cons _ _ _ h8, headNot_cons _ _ _ h9⟩

/-- The weak condition plus "no `'('` head" is the full RT-L2 condition. -/
theorem exprFollowB_of_op (r : List Char) (h1 : opFollowB r = true)
    (h2 : headNot '(' r = true) : exprFollowB r = true := by
  cases r with
  | nil => rfl
  | cons c cs =>
    simp only [opFollowB, Bool.not_eq_true', Bool.or_eq_false_iff] at h1
    simp only [headNot, Bool.not_eq_true'] at h2
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, g9⟩ := h1
    apply exprFollowB_cons
    simp [g1, g2, g3, g4, g5, g6, g7, g8, g9, h2]

theorem opFollowB_digit (c : Char) (cs : List Char) (h : isDigitB c = true) :
    opFollowB (c :: cs) = true := by
  apply opFollowB_cons
  simp [beqChar_digit_ne '+' c h (by decide), beqChar_digit_ne '-' c h (by decide),
    beqChar_digit_ne '*' c h (by decide), beqChar_digit_ne '/' c h (by decide),
    beqChar_digit_ne '%' c h (by decide), beqChar_digit_ne '<' c h (by decide),
    beqChar_digit_ne '=' c h (by decide), beqChar_digit_ne '&' c h (by decide),
    beqChar_digit_ne '|' c h (by decide)]

theorem opFollowB_idStart (c : Char) (cs : List Char) (h : isIdStartB c = true) :
    opFollowB (c :: cs) = true := by
  apply opFollowB_cons
  simp [beqChar_idStart_ne '+' c h (by decide), beqChar_idStart_ne '-' c h (by decide),
    beqChar_idStart_ne '*' c h (by decide), beqChar_idStart_ne '/' c h (by decide),
    beqChar_idStart_ne '%' c h (by decide), beqChar_idStart_ne '<' c h (by decide),
    beqChar_idStart_ne '=' c h (by decide), beqChar_idStart_ne '&' c h (by decide),
    beqChar_idStart_ne '|' c h (by decide)]

theorem headNot_paren_digit (c : Char) (cs : List Char) (h : isDigitB c = true) :
    headNot '(' (c :: cs) = true :=
  headNot_cons _ _ _ (beqChar_digit_ne '(' c h (by decide))

theorem headNot_paren_idStart (c : Char) (cs : List Char) (h : isIdStartB c = true) :
    headNot '(' (c :: cs) = true :=
  headNot_cons _ _ _ (beqChar_idStart_ne '(' c h (by decide))

/-! ## Head facts of canonical expression text

Canonical `printExpr` heads are a digit, `'('`, `'t'`, `'f'`, or an
identifier start — never an operator char, and `kw "def"` always dies on
them (for the identifier heads because a printable identifier is not the
keyword `def`). These drive the `FunDef*` star termination and the
program-level `Spacing`/follow bookkeeping. -/

theorem printExpr_head (e : Expr) (he : printableB e = true) (suffix : List Char) :
    opFollowB ((printExpr e).toList ++ suffix) = true ∧
    Derives shallotGrammar (kw "def") ((printExpr e).toList ++ suffix) .fail := by
  cases e with
  | intLit n =>
    by_cases hn : n < 0
    · have hEq : (printExpr (Expr.intLit n)).toList ++ suffix =
          '(' :: ' ' :: '-' :: ' ' ::
            (natDigits n.natAbs ++ (' ' :: ')' :: ' ' :: suffix)) := by
        simp [printExpr, hn, printNat, String.toList_append, String.toList_ofList,
          List.append_assoc]
      rw [hEq]
      exact ⟨opFollowB_cons _ _ (by decide),
        kw_head_fail _ "def" 'd' _ _ rfl (headNot_cons _ _ _ (by decide))⟩
    · cases hnd : natDigits n.natAbs with
      | nil => exact absurd hnd (natDigits_ne_nil n.natAbs)
      | cons d ds =>
        have hall := natDigits_all_digits n.natAbs
        rw [hnd] at hall
        simp only [List.all_cons, Bool.and_eq_true] at hall
        have hEq : (printExpr (Expr.intLit n)).toList ++ suffix =
            d :: (ds ++ ' ' :: suffix) := by
          simp [printExpr, hn, printNat, String.toList_append, String.toList_ofList,
            hnd, List.append_assoc]
        rw [hEq]
        exact ⟨opFollowB_digit d _ hall.1,
          kw_head_fail _ "def" 'd' _ _ rfl
            (headNot_cons _ _ _ (beqChar_digit_ne 'd' d hall.1 (by decide)))⟩
  | boolLit b =>
    cases b with
    | true =>
      have hEq : (printExpr (Expr.boolLit true)).toList ++ suffix =
          't' :: 'r' :: 'u' :: 'e' :: ' ' :: suffix := by
        simp [printExpr]
      rw [hEq]
      exact ⟨opFollowB_cons _ _ (by decide),
        kw_head_fail _ "def" 'd' _ _ rfl (headNot_cons _ _ _ (by decide))⟩
    | false =>
      have hEq : (printExpr (Expr.boolLit false)).toList ++ suffix =
          'f' :: 'a' :: 'l' :: 's' :: 'e' :: ' ' :: suffix := by
        simp [printExpr]
      rw [hEq]
      exact ⟨opFollowB_cons _ _ (by decide),
        kw_head_fail _ "def" 'd' _ _ rfl (headNot_cons _ _ _ (by decide))⟩
  | var x =>
    simp only [printableB] at he
    have hEq : (printExpr (Expr.var x)).toList ++ suffix = x.toList ++ ' ' :: suffix := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c, cs, hxl, hstart, -, hnk⟩ := validIdentB_spec x he
    have hall : x.toList.all isIdContB = true := validIdentB_all_idCont x he
    simp [keywords] at hnk
    refine ⟨?_, ?_⟩
    · rw [hxl]; exact opFollowB_idStart c _ hstart
    · refine kw_fail_of_litKills _ "def" _
        (litKills_of_ne "def".toList x.toList suffix (by decide) hall ?_)
      intro heq
      exact hnk.2.2.2.2.2.1 (String.toList_inj.mp heq.symm)
  | unop op e' =>
    have hEq : (printExpr (Expr.unop op e')).toList ++ suffix =
        '(' :: ' ' :: ((printUnOp op).toList ++
          ((printExpr e').toList ++ (')' :: ' ' :: suffix))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    exact ⟨opFollowB_cons _ _ (by decide),
      kw_head_fail _ "def" 'd' _ _ rfl (headNot_cons _ _ _ (by decide))⟩
  | binop op l r' =>
    have hEq : (printExpr (Expr.binop op l r')).toList ++ suffix =
        '(' :: ' ' :: ((printExpr l).toList ++ ((printBinOp op).toList ++
          ((printExpr r').toList ++ (')' :: ' ' :: suffix)))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    exact ⟨opFollowB_cons _ _ (by decide),
      kw_head_fail _ "def" 'd' _ _ rfl (headNot_cons _ _ _ (by decide))⟩
  | ite c t e' =>
    have hEq : (printExpr (Expr.ite c t e')).toList ++ suffix =
        '(' :: ' ' :: 'i' :: 'f' :: ' ' :: ((printExpr c).toList ++
          ('t' :: 'h' :: 'e' :: 'n' :: ' ' :: ((printExpr t).toList ++
            ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
              (')' :: ' ' :: suffix)))))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    exact ⟨opFollowB_cons _ _ (by decide),
      kw_head_fail _ "def" 'd' _ _ rfl (headNot_cons _ _ _ (by decide))⟩
  | letE x bound body =>
    have hEq : (printExpr (Expr.letE x bound body)).toList ++ suffix =
        '(' :: ' ' :: 'l' :: 'e' :: 't' :: ' ' :: (x.toList ++
          (' ' :: '=' :: ' ' :: ((printExpr bound).toList ++
            ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++
              (')' :: ' ' :: suffix)))))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    exact ⟨opFollowB_cons _ _ (by decide),
      kw_head_fail _ "def" 'd' _ _ rfl (headNot_cons _ _ _ (by decide))⟩
  | call f args =>
    simp only [printableB, Bool.and_eq_true] at he
    have hEq : (printExpr (Expr.call f args)).toList ++ suffix =
        f.toList ++ ' ' :: ('(' :: ' ' ::
          ((printArgs args).toList ++ (')' :: ' ' :: suffix))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c, cs, hxl, hstart, -, hnk⟩ := validIdentB_spec f he.1
    have hall : f.toList.all isIdContB = true := validIdentB_all_idCont f he.1
    simp [keywords] at hnk
    refine ⟨?_, ?_⟩
    · rw [hxl]; exact opFollowB_idStart c _ hstart
    · refine kw_fail_of_litKills _ "def" _
        (litKills_of_ne "def".toList f.toList _ (by decide) hall ?_)
      intro heq
      exact hnk.2.2.2.2.2.1 (String.toList_inj.mp heq.symm)

/-- A canonically-printed expression that is not `'('`-headed at the AST
level really has no `'('` at the head of its text. -/
theorem printExpr_headNot_paren (m : Expr) (hm : printableB m = true)
    (hp : parenHeadB m = false) (suffix : List Char) :
    headNot '(' ((printExpr m).toList ++ suffix) = true := by
  cases m with
  | intLit n =>
    have hn : ¬ n < 0 := by simpa [parenHeadB] using hp
    cases hnd : natDigits n.natAbs with
    | nil => exact absurd hnd (natDigits_ne_nil n.natAbs)
    | cons d ds =>
      have hall := natDigits_all_digits n.natAbs
      rw [hnd] at hall
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hEq : (printExpr (Expr.intLit n)).toList ++ suffix =
          d :: (ds ++ ' ' :: suffix) := by
        simp [printExpr, hn, printNat, String.toList_append, String.toList_ofList,
          hnd, List.append_assoc]
      rw [hEq]
      exact headNot_paren_digit d _ hall.1
  | boolLit b =>
    cases b with
    | true =>
      have hEq : (printExpr (Expr.boolLit true)).toList ++ suffix =
          't' :: 'r' :: 'u' :: 'e' :: ' ' :: suffix := by
        simp [printExpr]
      rw [hEq]
      exact headNot_cons _ _ _ (by decide)
    | false =>
      have hEq : (printExpr (Expr.boolLit false)).toList ++ suffix =
          'f' :: 'a' :: 'l' :: 's' :: 'e' :: ' ' :: suffix := by
        simp [printExpr]
      rw [hEq]
      exact headNot_cons _ _ _ (by decide)
  | var x =>
    simp only [printableB] at hm
    have hEq : (printExpr (Expr.var x)).toList ++ suffix = x.toList ++ ' ' :: suffix := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c, cs, hxl, hstart, -, -⟩ := validIdentB_spec x hm
    rw [hxl]
    exact headNot_paren_idStart c _ hstart
  | unop op e' => simp [parenHeadB] at hp
  | binop op l r' => simp [parenHeadB] at hp
  | ite c t e' => simp [parenHeadB] at hp
  | letE x bound body => simp [parenHeadB] at hp
  | call f args =>
    simp only [printableB, Bool.and_eq_true] at hm
    have hEq : (printExpr (Expr.call f args)).toList ++ suffix =
        f.toList ++ ' ' :: ('(' :: ' ' ::
          ((printArgs args).toList ++ (')' :: ' ' :: suffix))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c, cs, hxl, hstart, -, -⟩ := validIdentB_spec f hm.1
    rw [hxl]
    exact headNot_paren_idStart c _ hstart

/-! ## The Type layer -/

theorem printTy_int_toList (r : List Char) :
    (printTy .int).toList ++ r = 'i' :: 'n' :: 't' :: ' ' :: r := by
  simp [printTy]

theorem printTy_bool_toList (r : List Char) :
    (printTy .bool).toList ++ r = 'b' :: 'o' :: 'o' :: 'l' :: ' ' :: r := by
  simp [printTy]

theorem noWs_printTy (τ : Ty) (r : List Char) :
    noWsB ((printTy τ).toList ++ r) = true := by
  cases τ with
  | int => rw [printTy_int_toList]; exact noWsB_cons _ _ (by decide)
  | bool => rw [printTy_bool_toList]; exact noWsB_cons _ _ (by decide)

/-- The Type layer of RT-L3: `printTy τ` parses at `NT.type'` and the
tree recovers `τ` (`typeOf`). -/
theorem derives_printTy (τ : Ty) (r : List Char) (hr : noWsB r = true) :
    ∃ t, Derives shallotGrammar (.nt NT.type') ((printTy τ).toList ++ r)
      (.ok (.nodeNT NT.type' t) r) ∧ typeOf t = .ok τ := by
  cases τ with
  | int =>
    rw [printTy_int_toList]
    refine ⟨.choiceL (kwTree "int"), ?_, rfl⟩
    apply Derives.ntOk _ _ _ _ _ type'_rule
    exact Derives.altL _ _ _ _ _ (derives_kw "int" r hr)
  | bool =>
    rw [printTy_bool_toList]
    refine ⟨.choiceR (kwTree "bool"), ?_, rfl⟩
    apply Derives.ntOk _ _ _ _ _ type'_rule
    exact Derives.altR _ _ _ _ _
      (kw_head_fail _ "int" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))
      (derives_kw "bool" r hr)

/-! ## The Param/Params layer -/

/-- Canonical text of one parameter: `x : τ ` (trailing space from
`printTy`). -/
def paramText : String × Ty → List Char
  | (x, τ) => x.toList ++ ' ' :: ':' :: ' ' :: (printTy τ).toList

/-- The `(", " Param)*` region of a printed parameter list. -/
def paramsTailText : List (String × Ty) → List Char
  | [] => []
  | pr :: rest => ',' :: ' ' :: (paramText pr ++ paramsTailText rest)

theorem printParams_toList : ∀ (rest : List (String × Ty)) (x : String) (τ : Ty),
    (printParams ((x, τ) :: rest)).toList = paramText (x, τ) ++ paramsTailText rest := by
  intro rest
  induction rest with
  | nil =>
    intro x τ
    simp [printParams, paramText, paramsTailText, String.toList_append]
  | cons q rest' ih =>
    intro x τ
    obtain ⟨y, σ⟩ := q
    simp [printParams, paramText, paramsTailText, String.toList_append,
      ih y σ, List.append_assoc]

theorem noWs_paramText (x : String) (τ : Ty) (rest : List Char)
    (hx : validIdentB x = true) :
    noWsB (paramText (x, τ) ++ rest) = true := by
  have hEq : paramText (x, τ) ++ rest =
      x.toList ++ (' ' :: ':' :: ' ' :: ((printTy τ).toList ++ rest)) := by
    simp [paramText, List.append_assoc]
  rw [hEq]
  exact noWs_ident x _ hx

/-- One parameter parses at `NT.param`, recovering `(x, τ)` (`paramOf`). -/
theorem derives_param (x : String) (τ : Ty) (r : List Char)
    (hx : validIdentB x = true) (hr : noWsB r = true) :
    ∃ t, Derives shallotGrammar (.nt NT.param) (paramText (x, τ) ++ r)
      (.ok (.nodeNT NT.param t) r) ∧ paramOf t = .ok (x, τ) := by
  have hEq : paramText (x, τ) ++ r =
      x.toList ++ ' ' :: (':' :: ' ' :: ((printTy τ).toList ++ r)) := by
    simp [paramText, List.append_assoc]
  rw [hEq]
  obtain ⟨ti, hiD, hiV⟩ := derives_ident x (':' :: ' ' :: ((printTy τ).toList ++ r)) hx
    (noWsB_cons _ _ (by decide))
  obtain ⟨tt, htD, htV⟩ := derives_printTy τ r hr
  refine ⟨.seq (.nodeNT NT.ident ti) (.seq (tokTree ":") (.nodeNT NT.type' tt)), ?_, ?_⟩
  · apply Derives.ntOk _ _ _ _ _ param_rule
    exact Derives.seqOk _ _ _ _ _ _ _ hiD
      (Derives.seqOk _ _ _ _ _ _ _ (derives_tok ":" _ (noWs_printTy τ r)) htD)
  · simp only [paramOf, hiV, htV]; rfl

theorem paramsTail_headOk (ps : List (String × Ty)) (r : List Char) :
    noWsB (paramsTailText ps ++ (')' :: ' ' :: r)) = true := by
  cases ps with
  | nil => exact noWsB_cons _ _ (by decide)
  | cons pr rest => exact noWsB_cons _ _ (by decide)

/-- The `(", " Param)*` region parses as the star, stopping exactly at the
closing `') '`; `paramItems` recovers the list. -/
theorem derives_paramsTail : ∀ (ps : List (String × Ty)) (r : List Char),
    ps.all (fun pr => validIdentB pr.1) = true →
    ∃ t, Derives shallotGrammar (.star (.seq (tok ",") (.nt NT.param)))
      (paramsTailText ps ++ (')' :: ' ' :: r)) (.ok t (')' :: ' ' :: r)) ∧
      paramItems t = .ok ps := by
  intro ps
  induction ps with
  | nil =>
    intro r _
    refine ⟨.starNil, ?_, rfl⟩
    exact Derives.starNil _ _ (Derives.seqFail₁ _ _ _
      (tok_head_fail _ "," ',' [] _ rfl (headNot_cons _ _ _ (by decide))))
  | cons pr rest ih =>
    intro r hall
    obtain ⟨x, τ⟩ := pr
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have hEq : paramsTailText ((x, τ) :: rest) ++ (')' :: ' ' :: r) =
        ',' :: ' ' :: (paramText (x, τ) ++ (paramsTailText rest ++ (')' :: ' ' :: r))) := by
      simp [paramsTailText, List.append_assoc]
    rw [hEq]
    obtain ⟨tp, hpD, hpV⟩ := derives_param x τ (paramsTailText rest ++ (')' :: ' ' :: r))
      hall.1 (paramsTail_headOk rest r)
    obtain ⟨ts, hsD, hsV⟩ := ih r hall.2
    refine ⟨.starCons (.seq (tokTree ",") (.nodeNT NT.param tp)) ts, ?_, ?_⟩
    · exact Derives.starCons _ _ _ _ _ _
        (Derives.seqOk _ _ _ _ _ _ _
          (derives_tok "," _ (noWs_paramText x τ _ hall.1)) hpD) hsD
    · simp only [paramItems, hpV, hsV]; rfl

/-- The `Params? ")"`-region content: `printParams ps` parses as the
optional parameter list, stopping exactly at the closing `') '`. The
empty case takes the ε branch because `Param` (through `Ident`) fails on
`')'`. -/
theorem derives_printParamsOpt (ps : List (String × Ty)) (r : List Char)
    (hps : ps.all (fun pr => validIdentB pr.1) = true) :
    ∃ t, Derives shallotGrammar (PExp.opt (.nt NT.params))
      ((printParams ps).toList ++ (')' :: ' ' :: r)) (.ok t (')' :: ' ' :: r)) ∧
      ((∃ tf, t = .choiceR tf ∧ ps = []) ∨
       (∃ pT, t = .choiceL (.nodeNT NT.params pT) ∧ paramsOf pT = .ok ps)) := by
  cases ps with
  | nil =>
    have hEq : (printParams ([] : List (String × Ty))).toList ++ (')' :: ' ' :: r) =
        ')' :: ' ' :: r := by
      simp [printParams]
    rw [hEq]
    refine ⟨.choiceR (.leaf []), ?_, Or.inl ⟨.leaf [], rfl, rfl⟩⟩
    refine Derives.altR _ _ _ _ _ ?_ (Derives.eps _)
    apply Derives.ntFail _ _ _ params_rule
    apply Derives.seqFail₁
    apply Derives.ntFail _ _ _ param_rule
    apply Derives.seqFail₁
    exact ident_head_fail ')' _ (by decide) (by decide)
  | cons pr rest =>
    obtain ⟨x, τ⟩ := pr
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hEq : (printParams ((x, τ) :: rest)).toList ++ (')' :: ' ' :: r) =
        paramText (x, τ) ++ (paramsTailText rest ++ (')' :: ' ' :: r)) := by
      rw [printParams_toList rest x τ, List.append_assoc]
    rw [hEq]
    obtain ⟨tp, hpD, hpV⟩ := derives_param x τ (paramsTailText rest ++ (')' :: ' ' :: r))
      hps.1 (paramsTail_headOk rest r)
    obtain ⟨ts, hsD, hsV⟩ := derives_paramsTail rest r hps.2
    refine ⟨.choiceL (.nodeNT NT.params (.seq (.nodeNT NT.param tp) ts)), ?_,
      Or.inr ⟨_, rfl, ?_⟩⟩
    · apply Derives.altL
      apply Derives.ntOk _ _ _ _ _ params_rule
      exact Derives.seqOk _ _ _ _ _ _ _ hpD hsD
    · simp only [paramsOf, hpV, hsV]; rfl

theorem noWs_paramsRegion (ps : List (String × Ty)) (r : List Char)
    (hps : ps.all (fun pr => validIdentB pr.1) = true) :
    noWsB ((printParams ps).toList ++ (')' :: ' ' :: r)) = true := by
  cases ps with
  | nil =>
    have hEq : (printParams ([] : List (String × Ty))).toList ++ (')' :: ' ' :: r) =
        ')' :: ' ' :: r := by
      simp [printParams]
    rw [hEq]
    exact noWsB_cons _ _ (by decide)
  | cons pr rest =>
    obtain ⟨x, τ⟩ := pr
    simp only [List.all_cons, Bool.and_eq_true] at hps
    rw [printParams_toList rest x τ, List.append_assoc]
    exact noWs_paramText x τ _ hps.1

/-! ## The weak-follow expression climb

`climb_all` with `opFollowB` instead of `exprFollowB`: the ladder itself
never needs the `'('` exclusion (only `derives_print_primary`'s `var` case
does). -/

theorem climb_all_weak (e : Expr) (r : List Char) (t : PTree)
    (he : printableB e = true)
    (hp : Derives shallotGrammar (.nt NT.primary) ((printExpr e).toList ++ r)
      (.ok (.nodeNT NT.primary t) r))
    (hres : primaryOf t = .ok e)
    (hf : opFollowB r = true) :
    ∃ t', Derives shallotGrammar (.nt NT.expr) ((printExpr e).toList ++ r)
      (.ok (.nodeNT NT.expr t') r) ∧ exprOf t' = .ok e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := opFollowB_spec r hf
  obtain ⟨hkIf, hkLet, hkNeg, hkNot⟩ := (printExpr_text e he r).2
  obtain ⟨tu, hu, hru⟩ := climb_unary _ _ t e hp hres hkNeg hkNot
  obtain ⟨tm, hm, hrm⟩ := climb_mulE _ _ tu e hu hru h3 h4 h5
  obtain ⟨ta, hA, hra⟩ := climb_addE _ _ tm e hm hrm h1 h2
  obtain ⟨tc, hc, hrc⟩ := climb_cmpE _ _ ta e hA hra h6 h7
  obtain ⟨tn, hn, hrn⟩ := climb_andE _ _ tc e hc hrc h8
  obtain ⟨to, ho, hro⟩ := climb_orE _ _ tn e hn hrn h9
  exact climb_expr _ _ to e ho hro hkIf hkLet

/-! ## Paren-tolerant Primary for non-`var` expressions

The RT-L2 core (`derives_print_primary`) re-derived for every shape except
a bare variable, with the `headNot '(' r` hypothesis DROPPED — its proof
below is that of RT-L2 with the `var` case removed (the only case that
used the hypothesis); all inner recursive calls have safe follows and go
through the already-proven RT-L2 lemmas. -/

theorem derives_print_primary_nv (e : Expr) (r : List Char)
    (he : printableB e = true) (hnv : bareVarB e = false) (hws : noWsB r = true) :
    ∃ t, Derives shallotGrammar (.nt NT.primary) ((printExpr e).toList ++ r)
      (.ok (.nodeNT NT.primary t) r) ∧ primaryOf t = .ok e := by
  cases e with
  | intLit n =>
    by_cases hn : n < 0
    · -- `( - digits ) ` → paren alternative, Unary's "-" branch, Number
      have hdig : noWsB (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r)) = true ∧
          Derives shallotGrammar (.lit ['-'])
            (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r)) .fail ∧
          Derives shallotGrammar (.lit ['!'])
            (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r)) .fail := by
        cases hnd : natDigits n.natAbs with
        | nil => exact absurd hnd (natDigits_ne_nil _)
        | cons d ds =>
          have hall := natDigits_all_digits n.natAbs
          rw [hnd] at hall
          simp only [List.all_cons, Bool.and_eq_true] at hall
          exact ⟨noWsB_cons _ _ (isWsB_digit d hall.1),
            lit_head_fail _ '-' [] _
              (headNot_cons _ _ _ (beqChar_digit_ne '-' d hall.1 (by decide))),
            lit_head_fail _ '!' [] _
              (headNot_cons _ _ _ (beqChar_digit_ne '!' d hall.1 (by decide)))⟩
      obtain ⟨hnwD, hkNeg, hkNot⟩ := hdig
      have hEq : (printExpr (Expr.intLit n)).toList ++ r =
          '(' :: ' ' :: ('-' :: ' ' :: (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r))) := by
        simp [printExpr, hn, printNat, String.toList_ofList, String.toList_append,
          List.append_assoc]
      rw [hEq]
      obtain ⟨tn, hnD, hnV⟩ := derives_number n.natAbs (')' :: ' ' :: r)
        (noWsB_cons _ _ (by decide))
      have hprim : Derives shallotGrammar (.nt NT.primary)
          (natDigits n.natAbs ++ ' ' :: (')' :: ' ' :: r))
          (.ok (.nodeNT NT.primary (.choiceL (.nodeNT NT.number tn))) (')' :: ' ' :: r)) :=
        Derives.ntOk _ _ _ _ _ primary_rule (Derives.altL _ _ _ _ _ hnD)
      have hpv : primaryOf (.choiceL (.nodeNT NT.number tn)) =
          .ok (.intLit (Int.ofNat n.natAbs)) := by
        simp only [primaryOf, hnV]; rfl
      obtain ⟨tu, hu, huv⟩ := climb_unary _ _ _ _ hprim hpv hkNeg hkNot
      have hU2 := Derives.ntOk _ _ _ _ _ unary_rule (Derives.altL _ _ _ _ _
        (Derives.seqOk _ _ _ _ _ _ _ (derives_tok "-" _ hnwD) hu))
      have hU2v : unaryOf (.choiceL (.seq (tokTree "-") (.nodeNT NT.unary tu))) =
          .ok (.intLit n) := by
        have h1 : unaryOf (.choiceL (.seq (tokTree "-") (.nodeNT NT.unary tu))) =
            .ok (.intLit (-(Int.ofNat n.natAbs))) := by
          simp only [unaryOf, huv]; rfl
        rw [h1, show -(Int.ofNat n.natAbs) = n from by
          have hc : Int.ofNat n.natAbs = (n.natAbs : Int) := rfl
          rw [hc]; omega]
      obtain ⟨tE, hEd, hEv⟩ := climb_from_unary _ _ _ _ hU2 hU2v
        (exprFollowB_cons _ _ (by decide))
        (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))
        (kw_head_fail _ "let" 'l' _ _ rfl (headNot_cons _ _ _ (by decide)))
      exact derives_primary_paren _ r tE _ hEd hEv (noWsB_cons _ _ (by decide)) hws
    · -- bare digits → Number alternative
      have hEq : (printExpr (Expr.intLit n)).toList ++ r = natDigits n.natAbs ++ ' ' :: r := by
        simp [printExpr, hn, printNat, String.toList_ofList, String.toList_append,
          List.append_assoc]
      rw [hEq]
      obtain ⟨tn, hnD, hnV⟩ := derives_number n.natAbs r hws
      rw [show Int.ofNat n.natAbs = n from by
        have hc : Int.ofNat n.natAbs = (n.natAbs : Int) := rfl
        rw [hc]; omega] at hnV
      refine ⟨.choiceL (.nodeNT NT.number tn), ?_, ?_⟩
      · exact Derives.ntOk _ _ _ _ _ primary_rule (Derives.altL _ _ _ _ _ hnD)
      · simp only [primaryOf, hnV]; rfl
  | boolLit b =>
    cases b with
    | true =>
      have hEq : (printExpr (Expr.boolLit true)).toList ++ r =
          't' :: 'r' :: 'u' :: 'e' :: ' ' :: r := by
        simp [printExpr]
      rw [hEq]
      refine ⟨.choiceR (.choiceL (kwTree "true")), ?_, by simp [primaryOf]⟩
      apply Derives.ntOk _ _ _ _ _ primary_rule
      exact Derives.altR _ _ _ _ _ (number_head_fail 't' _ (by decide))
        (Derives.altL _ _ _ _ _ (derives_kw "true" r hws))
    | false =>
      have hEq : (printExpr (Expr.boolLit false)).toList ++ r =
          'f' :: 'a' :: 'l' :: 's' :: 'e' :: ' ' :: r := by
        simp [printExpr]
      rw [hEq]
      refine ⟨.choiceR (.choiceR (.choiceL (kwTree "false"))), ?_, by simp [primaryOf]⟩
      apply Derives.ntOk _ _ _ _ _ primary_rule
      refine Derives.altR _ _ _ _ _ (number_head_fail 'f' _ (by decide)) ?_
      refine Derives.altR _ _ _ _ _
        (kw_head_fail _ "true" 't' _ _ rfl (headNot_cons _ _ _ (by decide))) ?_
      exact Derives.altL _ _ _ _ _ (derives_kw "false" r hws)
  | var x => simp [bareVarB] at hnv
  | unop op e' =>
    cases op with
    | neg =>
      have hne : ∀ m : Int, e' ≠ .intLit m := by
        intro m hm
        subst hm
        simp [printableB] at he
      have he' : printableB e' = true := by
        cases e' <;> simp_all [printableB]
      have hEq : (printExpr (Expr.unop .neg e')).toList ++ r =
          '(' :: ' ' :: ('-' :: ' ' :: ((printExpr e').toList ++ (')' :: ' ' :: r))) := by
        simp [printExpr, printUnOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwS, hkS⟩ := printExpr_text e' he' (')' :: ' ' :: r)
      obtain ⟨tp, hp, hpv⟩ := derives_print_primary e' (')' :: ' ' :: r) he'
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tu, hu, huv⟩ := climb_unary _ _ tp e' hp hpv hkS.litNeg hkS.litNot
      have hU2 := Derives.ntOk _ _ _ _ _ unary_rule (Derives.altL _ _ _ _ _
        (Derives.seqOk _ _ _ _ _ _ _ (derives_tok "-" _ hnwS) hu))
      have hU2v : unaryOf (.choiceL (.seq (tokTree "-") (.nodeNT NT.unary tu))) =
          .ok (.unop .neg e') := by
        simp only [unaryOf, huv]
        cases e' <;> first | (exact absurd rfl (hne _)) | rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_unary _ _ _ _ hU2 hU2v
        (exprFollowB_cons _ _ (by decide))
        (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))
        (kw_head_fail _ "let" 'l' _ _ rfl (headNot_cons _ _ _ (by decide)))
      exact derives_primary_paren _ r tE _ hEd hEv (noWsB_cons _ _ (by decide)) hws
    | notB =>
      have he' : printableB e' = true := by
        simpa [printableB] using he
      have hEq : (printExpr (Expr.unop .notB e')).toList ++ r =
          '(' :: ' ' :: ('!' :: ' ' :: ((printExpr e').toList ++ (')' :: ' ' :: r))) := by
        simp [printExpr, printUnOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwS, hkS⟩ := printExpr_text e' he' (')' :: ' ' :: r)
      obtain ⟨tp, hp, hpv⟩ := derives_print_primary e' (')' :: ' ' :: r) he'
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tu, hu, huv⟩ := climb_unary _ _ tp e' hp hpv hkS.litNeg hkS.litNot
      have hU2 := Derives.ntOk _ _ _ _ _ unary_rule (Derives.altR _ _ _ _ _
        (Derives.seqFail₁ _ _ _
          (tok_head_fail _ "-" '-' [] _ rfl (headNot_cons _ _ _ (by decide))))
        (Derives.altL _ _ _ _ _
          (Derives.seqOk _ _ _ _ _ _ _ (derives_tok "!" _ hnwS) hu)))
      have hU2v : unaryOf (.choiceR (.choiceL (.seq (tokTree "!") (.nodeNT NT.unary tu)))) =
          .ok (.unop .notB e') := by
        simp only [unaryOf, huv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_unary _ _ _ _ hU2 hU2v
        (exprFollowB_cons _ _ (by decide))
        (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))
        (kw_head_fail _ "let" 'l' _ _ rfl (headNot_cons _ _ _ (by decide)))
      exact derives_primary_paren _ r tE _ hEd hEv (noWsB_cons _ _ (by decide)) hws
  | binop op l r' =>
    cases op with
    | add =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .add l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('+' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('+' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tmB, hmB, hmBv⟩ := operand_to_mulE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('+' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tmA, hmA, hmAv⟩ := operand_to_mulE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hAdd := assemble_addE _ _ _ _ tmA tmB (.choiceL (tokTree "+")) hmA
        (Derives.altL _ _ _ _ _ (derives_tok "+" _ hnwB)) hmB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      have hAddV : addOf (.seq (.nodeNT NT.mulE tmA)
          (.starCons (.seq (.choiceL (tokTree "+")) (.nodeNT NT.mulE tmB)) .starNil)) =
          .ok (.binop .add l r') := by
        simp only [addOf, hmAv, goAdd, hmBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_addE _ _ _ _ hAdd hAddV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | sub =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .sub l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('-' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('-' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tmB, hmB, hmBv⟩ := operand_to_mulE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('-' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tmA, hmA, hmAv⟩ := operand_to_mulE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hAdd := assemble_addE _ _ _ _ tmA tmB (.choiceR (tokTree "-")) hmA
        (Derives.altR _ _ _ _ _
          (tok_head_fail _ "+" '+' [] _ rfl (headNot_cons _ _ _ (by decide)))
          (derives_tok "-" _ hnwB)) hmB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      have hAddV : addOf (.seq (.nodeNT NT.mulE tmA)
          (.starCons (.seq (.choiceR (tokTree "-")) (.nodeNT NT.mulE tmB)) .starNil)) =
          .ok (.binop .sub l r') := by
        simp only [addOf, hmAv, goAdd, hmBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_addE _ _ _ _ hAdd hAddV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | mul =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .mul l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('*' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('*' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuB, huB, huBv⟩ := operand_to_unary r' _ tpB he.2 hpB hpBv
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('*' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuA, huA, huAv⟩ := operand_to_unary l _ tpA he.1 hpA hpAv
      have hMul := assemble_mulE _ _ _ _ tuA tuB (.choiceL (tokTree "*")) huA
        (Derives.altL _ _ _ _ _ (derives_tok "*" _ hnwB)) huB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hMulV : mulOf (.seq (.nodeNT NT.unary tuA)
          (.starCons (.seq (.choiceL (tokTree "*")) (.nodeNT NT.unary tuB)) .starNil)) =
          .ok (.binop .mul l r') := by
        simp only [mulOf, huAv, goMul, huBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_mulE _ _ _ _ hMul hMulV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | div =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .div l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('/' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('/' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuB, huB, huBv⟩ := operand_to_unary r' _ tpB he.2 hpB hpBv
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('/' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuA, huA, huAv⟩ := operand_to_unary l _ tpA he.1 hpA hpAv
      have hMul := assemble_mulE _ _ _ _ tuA tuB (.choiceR (.choiceL (tokTree "/"))) huA
        (Derives.altR _ _ _ _ _
          (tok_head_fail _ "*" '*' [] _ rfl (headNot_cons _ _ _ (by decide)))
          (Derives.altL _ _ _ _ _ (derives_tok "/" _ hnwB))) huB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hMulV : mulOf (.seq (.nodeNT NT.unary tuA)
          (.starCons (.seq (.choiceR (.choiceL (tokTree "/"))) (.nodeNT NT.unary tuB))
            .starNil)) = .ok (.binop .div l r') := by
        simp only [mulOf, huAv, goMul, huBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_mulE _ _ _ _ hMul hMulV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | mod =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .mod l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('%' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('%' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuB, huB, huBv⟩ := operand_to_unary r' _ tpB he.2 hpB hpBv
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('%' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tuA, huA, huAv⟩ := operand_to_unary l _ tpA he.1 hpA hpAv
      have hMul := assemble_mulE _ _ _ _ tuA tuB
        (.choiceR (.choiceR (tokTree "%"))) huA
        (Derives.altR _ _ _ _ _
          (tok_head_fail _ "*" '*' [] _ rfl (headNot_cons _ _ _ (by decide)))
          (Derives.altR _ _ _ _ _
            (tok_head_fail _ "/" '/' [] _ rfl (headNot_cons _ _ _ (by decide)))
            (derives_tok "%" _ hnwB))) huB
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hMulV : mulOf (.seq (.nodeNT NT.unary tuA)
          (.starCons (.seq (.choiceR (.choiceR (tokTree "%"))) (.nodeNT NT.unary tuB))
            .starNil)) = .ok (.binop .mod l r') := by
        simp only [mulOf, huAv, goMul, huBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_mulE _ _ _ _ hMul hMulV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | lt =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .lt l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('<' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('<' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taB, haB, haBv⟩ := operand_to_addE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('<' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taA, haA, haAv⟩ := operand_to_addE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hCmp := assemble_cmpE _ _ _ _ taA taB
        (.choiceR (.choiceL (chrGuardTree '<'))) haA
        (Derives.altR _ _ _ _ _
          (Derives.seqFail₁ _ _ _ (Derives.litFail _ _ rfl))
          (Derives.altL _ _ _ _ _ (derives_ltTok _ hnwB))) haB
      have hCmpV : cmpOf (.seq (.nodeNT NT.addE taA)
          (.choiceL (.seq (.choiceR (.choiceL (chrGuardTree '<')))
            (.nodeNT NT.addE taB)))) = .ok (.binop .lt l r') := by
        simp only [cmpOf, haAv, haBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_cmpE _ _ _ _ hCmp hCmpV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | le =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .le l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('<' :: '=' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('<' :: '=' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taB, haB, haBv⟩ := operand_to_addE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('<' :: '=' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taA, haA, haAv⟩ := operand_to_addE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hCmp := assemble_cmpE _ _ _ _ taA taB (.choiceL (tokTree "<=")) haA
        (Derives.altL _ _ _ _ _ (derives_tok "<=" _ hnwB)) haB
      have hCmpV : cmpOf (.seq (.nodeNT NT.addE taA)
          (.choiceL (.seq (.choiceL (tokTree "<=")) (.nodeNT NT.addE taB)))) =
          .ok (.binop .le l r') := by
        simp only [cmpOf, haAv, haBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_cmpE _ _ _ _ hCmp hCmpV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | eqI =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .eqI l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('=' :: '=' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('=' :: '=' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taB, haB, haBv⟩ := operand_to_addE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('=' :: '=' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨taA, haA, haAv⟩ := operand_to_addE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hCmp := assemble_cmpE _ _ _ _ taA taB
        (.choiceR (.choiceR (tokTree "=="))) haA
        (Derives.altR _ _ _ _ _
          (tok_head_fail _ "<=" '<' ['='] _ rfl (headNot_cons _ _ _ (by decide)))
          (Derives.altR _ _ _ _ _
            (ltTok_head_fail _ _ (headNot_cons _ _ _ (by decide)))
            (derives_tok "==" _ hnwB))) haB
      have hCmpV : cmpOf (.seq (.nodeNT NT.addE taA)
          (.choiceL (.seq (.choiceR (.choiceR (tokTree "=="))) (.nodeNT NT.addE taB)))) =
          .ok (.binop .eqI l r') := by
        simp only [cmpOf, haAv, haBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_cmpE _ _ _ _ hCmp hCmpV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | eqB =>
      simp [printableB] at he
    | andB =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .andB l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('&' :: '&' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('&' :: '&' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tcB, hcB, hcBv⟩ := operand_to_cmpE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('&' :: '&' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tcA, hcA, hcAv⟩ := operand_to_cmpE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide))
      have hAnd := assemble_andE _ _ _ _ tcA tcB (tokTree "&&") hcA
        (derives_tok "&&" _ hnwB) hcB (headNot_cons _ _ _ (by decide))
      have hAndV : andOf (.seq (.nodeNT NT.cmpE tcA)
          (.starCons (.seq (tokTree "&&") (.nodeNT NT.cmpE tcB)) .starNil)) =
          .ok (.binop .andB l r') := by
        simp only [andOf, hcAv, goAnd, hcBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_from_andE _ _ _ _ hAnd hAndV
        (exprFollowB_cons _ _ (by decide)) hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
    | orB =>
      simp only [printableB, Bool.and_eq_true] at he
      have hEq : (printExpr (Expr.binop .orB l r')).toList ++ r =
          '(' :: ' ' :: ((printExpr l).toList ++ ('|' :: '|' :: ' ' ::
            ((printExpr r').toList ++ (')' :: ' ' :: r)))) := by
        simp [printExpr, printBinOp, String.toList_append, List.append_assoc]
      rw [hEq]
      obtain ⟨hnwB, -⟩ := printExpr_text r' he.2 (')' :: ' ' :: r)
      obtain ⟨hnwA, hkA⟩ := printExpr_text l he.1
        ('|' :: '|' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r)))
      obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary r' (')' :: ' ' :: r) he.2
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tnB, hnB, hnBv⟩ := operand_to_andE r' _ tpB he.2 hpB hpBv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tpA, hpA, hpAv⟩ := derives_print_primary l
        ('|' :: '|' :: ' ' :: ((printExpr r').toList ++ (')' :: ' ' :: r))) he.1
        (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      obtain ⟨tnA, hnA, hnAv⟩ := operand_to_andE l _ tpA he.1 hpA hpAv
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
        (headNot_cons _ _ _ (by decide)) (headNot_cons _ _ _ (by decide))
      have hOr := assemble_orE _ _ _ _ tnA tnB (tokTree "||") hnA
        (derives_tok "||" _ hnwB) hnB (headNot_cons _ _ _ (by decide))
      have hOrV : orOf (.seq (.nodeNT NT.andE tnA)
          (.starCons (.seq (tokTree "||") (.nodeNT NT.andE tnB)) .starNil)) =
          .ok (.binop .orB l r') := by
        simp only [orOf, hnAv, goOr, hnBv]; rfl
      obtain ⟨tE, hEd, hEv⟩ := climb_expr _ _ _ _ hOr hOrV hkA.kwIf hkA.kwLet
      exact derives_primary_paren _ r tE _ hEd hEv hnwA hws
  | ite c t e' =>
    simp only [printableB, Bool.and_eq_true] at he
    obtain ⟨⟨hc, ht2⟩, he'⟩ := he
    have hEq : (printExpr (Expr.ite c t e')).toList ++ r =
        '(' :: ' ' :: ('i' :: 'f' :: ' ' :: ((printExpr c).toList ++
          ('t' :: 'h' :: 'e' :: 'n' :: ' ' :: ((printExpr t).toList ++
            ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
              (')' :: ' ' :: r))))))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨tpC, hpC, hpCv⟩ := derives_print_primary c
      ('t' :: 'h' :: 'e' :: 'n' :: ' ' :: ((printExpr t).toList ++
        ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
          (')' :: ' ' :: r))))) hc
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tC, hCd, hCv⟩ := climb_all c _ tpC hc hpC hpCv (exprFollowB_cons _ _ (by decide))
    obtain ⟨tpT, hpT, hpTv⟩ := derives_print_primary t
      ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++ (')' :: ' ' :: r))) ht2
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tT, hTd, hTv⟩ := climb_all t _ tpT ht2 hpT hpTv (exprFollowB_cons _ _ (by decide))
    obtain ⟨tpE, hpE, hpEv⟩ := derives_print_primary e' (')' :: ' ' :: r) he'
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tEe, hEd, hEv⟩ := climb_all e' _ tpE he' hpE hpEv (exprFollowB_cons _ _ (by decide))
    have hIf := Derives.ntOk _ _ _ _ _ ifExpr_rule
      (Derives.seqOk _ _ _ _ _ _ _
        (derives_kw "if" _ (printExpr_text c hc
          ('t' :: 'h' :: 'e' :: 'n' :: ' ' :: ((printExpr t).toList ++
            ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
              (')' :: ' ' :: r)))))).1)
        (Derives.seqOk _ _ _ _ _ _ _ hCd
          (Derives.seqOk _ _ _ _ _ _ _
            (derives_kw "then" _ (printExpr_text t ht2
              ('e' :: 'l' :: 's' :: 'e' :: ' ' :: ((printExpr e').toList ++
                (')' :: ' ' :: r)))).1)
            (Derives.seqOk _ _ _ _ _ _ _ hTd
              (Derives.seqOk _ _ _ _ _ _ _
                (derives_kw "else" _ (printExpr_text e' he' (')' :: ' ' :: r)).1)
                hEd)))))
    have hEx := Derives.ntOk _ _ _ _ _ expr_rule (Derives.altL _ _ _ _ _ hIf)
    have hExV : exprOf (.choiceL (.nodeNT NT.ifExpr
        (.seq (kwTree "if") (.seq (.nodeNT NT.expr tC) (.seq (kwTree "then")
          (.seq (.nodeNT NT.expr tT) (.seq (kwTree "else") (.nodeNT NT.expr tEe)))))))) =
        .ok (.ite c t e') := by
      simp only [exprOf, ifOf, hCv, hTv, hEv]; rfl
    exact derives_primary_paren _ r _ _ hEx hExV (noWsB_cons _ _ (by decide)) hws
  | letE x bound body =>
    simp only [printableB, Bool.and_eq_true] at he
    obtain ⟨⟨hx, hb⟩, hbd⟩ := he
    have hEq : (printExpr (Expr.letE x bound body)).toList ++ r =
        '(' :: ' ' :: ('l' :: 'e' :: 't' :: ' ' :: (x.toList ++
          (' ' :: '=' :: ' ' :: ((printExpr bound).toList ++
            ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++ (')' :: ' ' :: r))))))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨ti, hiD, hiV⟩ := derives_ident x
      ('=' :: ' ' :: ((printExpr bound).toList ++
        ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++ (')' :: ' ' :: r))))) hx
      (noWsB_cons _ _ (by decide))
    obtain ⟨tpB, hpB, hpBv⟩ := derives_print_primary bound
      ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++ (')' :: ' ' :: r))) hb
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tB, hBd, hBv⟩ := climb_all bound _ tpB hb hpB hpBv
      (exprFollowB_cons _ _ (by decide))
    obtain ⟨tpD, hpD, hpDv⟩ := derives_print_primary body (')' :: ' ' :: r) hbd
      (noWsB_cons _ _ (by decide)) (headNot_cons _ _ _ (by decide))
    obtain ⟨tD, hDd, hDv⟩ := climb_all body _ tpD hbd hpD hpDv
      (exprFollowB_cons _ _ (by decide))
    have hLet := Derives.ntOk _ _ _ _ _ letExpr_rule
      (Derives.seqOk _ _ _ _ _ _ _ (derives_kw "let" _ (noWs_ident x _ hx))
        (Derives.seqOk _ _ _ _ _ _ _ hiD
          (Derives.seqOk _ _ _ _ _ _ _
            (derives_eqTok _ (printExpr_text bound hb
              ('i' :: 'n' :: ' ' :: ((printExpr body).toList ++ (')' :: ' ' :: r)))).1)
            (Derives.seqOk _ _ _ _ _ _ _ hBd
              (Derives.seqOk _ _ _ _ _ _ _
                (derives_kw "in" _ (printExpr_text body hbd (')' :: ' ' :: r)).1)
                hDd)))))
    have hEx := Derives.ntOk _ _ _ _ _ expr_rule
      (Derives.altR _ _ _ _ _
        (Derives.ntFail _ _ _ ifExpr_rule (Derives.seqFail₁ _ _ _
          (kw_head_fail _ "if" 'i' _ _ rfl (headNot_cons _ _ _ (by decide)))))
        (Derives.altL _ _ _ _ _ hLet))
    have hExV : exprOf (.choiceR (.choiceL (.nodeNT NT.letExpr
        (.seq (kwTree "let") (.seq (.nodeNT NT.ident ti) (.seq (chrGuardTree '=')
          (.seq (.nodeNT NT.expr tB) (.seq (kwTree "in") (.nodeNT NT.expr tD))))))))) =
        .ok (.letE x bound body) := by
      simp only [exprOf, letOf, hiV, hBv, hDv]; rfl
    exact derives_primary_paren _ r _ _ hEx hExV (noWsB_cons _ _ (by decide)) hws
  | call f args =>
    simp only [printableB, Bool.and_eq_true] at he
    have hEq : (printExpr (Expr.call f args)).toList ++ r =
        f.toList ++ ' ' :: ('(' :: ' ' ::
          ((printArgs args).toList ++ (')' :: ' ' :: r))) := by
      simp [printExpr, String.toList_append, List.append_assoc]
    rw [hEq]
    obtain ⟨c0, cs0, hxl, hstart, -, -⟩ := validIdentB_spec f he.1
    obtain ⟨-, -, hTr, hFa⟩ := ident_kws_fail f
      ('(' :: ' ' :: ((printArgs args).toList ++ (')' :: ' ' :: r))) he.1
    obtain ⟨ti, hiD, hiV⟩ := derives_ident f
      ('(' :: ' ' :: ((printArgs args).toList ++ (')' :: ' ' :: r))) he.1
      (noWsB_cons _ _ (by decide))
    have hnum : Derives shallotGrammar (.nt NT.number)
        (f.toList ++ ' ' :: ('(' :: ' ' ::
          ((printArgs args).toList ++ (')' :: ' ' :: r)))) .fail := by
      rw [hxl]
      exact number_head_fail c0 _ (isDigitB_idStart c0 hstart)
    have hnwArgs : noWsB ((printArgs args).toList ++ (')' :: ' ' :: r)) = true := by
      cases args with
      | nil =>
        have h0 : (printArgs Args.nil).toList = ([] : List Char) := by simp [printArgs]
        rw [h0]
        exact noWsB_cons _ _ (by decide)
      | cons e0 rest0 =>
        rw [printArgs_cons_toList, List.append_assoc]
        have ha0 : printableB e0 = true := by
          have h2 := he.2
          simp only [printableArgsB, Bool.and_eq_true] at h2
          exact h2.1
        exact (printExpr_text e0 ha0 _).1
    obtain ⟨taT, haD, haV⟩ := derives_print_argsOpt args r he.2
    refine ⟨.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT NT.call
      (.seq (.nodeNT NT.ident ti) (.seq (tokTree "(") (.seq taT (tokTree ")")))))))),
      ?_, ?_⟩
    · apply Derives.ntOk _ _ _ _ _ primary_rule
      refine Derives.altR _ _ _ _ _ hnum ?_
      refine Derives.altR _ _ _ _ _ hTr ?_
      refine Derives.altR _ _ _ _ _ hFa ?_
      apply Derives.altL
      apply Derives.ntOk _ _ _ _ _ call_rule
      refine Derives.seqOk _ _ _ _ _ _ _ hiD ?_
      refine Derives.seqOk _ _ _ _ _ _ _ (derives_tok "(" _ hnwArgs) ?_
      exact Derives.seqOk _ _ _ _ _ _ _ haD (derives_tok ")" r hws)
    · cases haV with
      | inl h =>
        obtain ⟨tf, h1, h2⟩ := h
        subst h1; subst h2
        simp only [primaryOf]
        exact callOf_decode_nil ti tf _ _ f hiV
      | inr h =>
        obtain ⟨alT, h1, h2⟩ := h
        subst h1
        simp only [primaryOf]
        exact callOf_decode_cons ti alT _ _ f args hiV h2

/-- The body-position expression payoff: the full RT-L2 statement when the
follow satisfies `exprFollowB`, and the paren-tolerant variant when the
body is not a bare variable. This is exactly what a `FunDef` body needs:
its follow is either the next `"def …"` (full condition holds) or `main`'s
text (possibly `'('`-headed — excluded for bare-`var` bodies by `sepOkB`). -/
theorem derives_printExpr_body (e : Expr) (r : List Char)
    (he : printableB e = true) (hws : noWsB r = true)
    (hf : exprFollowB r = true ∨ (bareVarB e = false ∧ opFollowB r = true)) :
    ∃ t, Derives shallotGrammar (.nt NT.expr) ((printExpr e).toList ++ r)
      (.ok (.nodeNT NT.expr t) r) ∧ exprOf t = .ok e := by
  cases hf with
  | inl h => exact derives_printExpr e r he hws h
  | inr h =>
    obtain ⟨tp, hp, hpv⟩ := derives_print_primary_nv e r he h.1 hws
    exact climb_all_weak e r tp he hp hpv h.2

/-! ## The FunDef layer -/

theorem printFun_toList (d : FunDef) (r : List Char) :
    (printFun d).toList ++ r =
      'd' :: 'e' :: 'f' :: ' ' :: (d.name.toList ++ ' ' :: ('(' :: ' ' ::
        ((printParams d.params).toList ++ (')' :: ' ' :: (':' :: ' ' ::
          ((printTy d.retTy).toList ++ ('=' :: ' ' ::
            ((printExpr d.body).toList ++ r)))))))) := by
  simp [printFun, String.toList_append, List.append_assoc]

/-- `funDefOf` decode, empty parameter list. -/
theorem funDefOf_decode_nil (t1 t3 t5 t6 t8 tf ti tty tb : PTree)
    (name : String) (retTy : Ty) (body : Expr)
    (hiV : identName ti = .ok name) (htV : typeOf tty = .ok retTy)
    (hbV : exprOf tb = .ok body) :
    funDefOf (.seq t1 (.seq (.nodeNT NT.ident ti) (.seq t3 (.seq (.choiceR tf)
      (.seq t5 (.seq t6 (.seq (.nodeNT NT.type' tty)
        (.seq t8 (.nodeNT NT.expr tb))))))))) =
      .ok { name := name, params := [], retTy := retTy, body := body } := by
  simp only [funDefOf]
  rw [hiV, htV, hbV]
  rfl

/-- `funDefOf` decode, non-empty parameter list. -/
theorem funDefOf_decode_cons (t1 t3 t5 t6 t8 ti pT tty tb : PTree)
    (name : String) (ps : List (String × Ty)) (retTy : Ty) (body : Expr)
    (hiV : identName ti = .ok name) (hpV : paramsOf pT = .ok ps)
    (htV : typeOf tty = .ok retTy) (hbV : exprOf tb = .ok body) :
    funDefOf (.seq t1 (.seq (.nodeNT NT.ident ti)
      (.seq t3 (.seq (.choiceL (.nodeNT NT.params pT))
        (.seq t5 (.seq t6 (.seq (.nodeNT NT.type' tty)
          (.seq t8 (.nodeNT NT.expr tb))))))))) =
      .ok { name := name, params := ps, retTy := retTy, body := body } := by
  simp only [funDefOf]
  rw [hiV, hpV, htV, hbV]
  rfl

/-- The FunDef layer of RT-L3: `printFun d` parses at `NT.funDef`
consuming exactly the printed text, and `funDefOf` recovers `d`. The
follow condition is that of `derives_printExpr_body` (the body is the last
component of a `FunDef`). -/
theorem derives_printFun (d : FunDef) (r : List Char)
    (hd : printableFunB d = true) (hws : noWsB r = true)
    (hf : exprFollowB r = true ∨ (bareVarB d.body = false ∧ opFollowB r = true)) :
    ∃ t, Derives shallotGrammar (.nt NT.funDef) ((printFun d).toList ++ r)
      (.ok (.nodeNT NT.funDef t) r) ∧ funDefOf t = .ok d := by
  simp only [printableFunB, Bool.and_eq_true] at hd
  obtain ⟨⟨hname, hparams⟩, hbody⟩ := hd
  rw [printFun_toList]
  obtain ⟨tb, hbD, hbV⟩ := derives_printExpr_body d.body r hbody hws hf
  have hnwBody : noWsB ((printExpr d.body).toList ++ r) = true :=
    (printExpr_text d.body hbody r).1
  obtain ⟨tty, htyD, htyV⟩ := derives_printTy d.retTy
    ('=' :: ' ' :: ((printExpr d.body).toList ++ r)) (noWsB_cons _ _ (by decide))
  obtain ⟨tps, hpsD, hpsV⟩ := derives_printParamsOpt d.params
    (':' :: ' ' :: ((printTy d.retTy).toList ++ ('=' :: ' ' ::
      ((printExpr d.body).toList ++ r)))) hparams
  obtain ⟨ti, hiD, hiV⟩ := derives_ident d.name
    ('(' :: ' ' :: ((printParams d.params).toList ++ (')' :: ' ' :: (':' :: ' ' ::
      ((printTy d.retTy).toList ++ ('=' :: ' ' ::
        ((printExpr d.body).toList ++ r))))))) hname (noWsB_cons _ _ (by decide))
  refine ⟨.seq (kwTree "def") (.seq (.nodeNT NT.ident ti) (.seq (tokTree "(")
    (.seq tps (.seq (tokTree ")") (.seq (tokTree ":") (.seq (.nodeNT NT.type' tty)
      (.seq (chrGuardTree '=') (.nodeNT NT.expr tb)))))))), ?_, ?_⟩
  · apply Derives.ntOk _ _ _ _ _ funDef_rule
    refine Derives.seqOk _ _ _ _ _ _ _
      (derives_kw "def" _ (noWs_ident d.name _ hname)) ?_
    refine Derives.seqOk _ _ _ _ _ _ _ hiD ?_
    refine Derives.seqOk _ _ _ _ _ _ _
      (derives_tok "(" _ (noWs_paramsRegion d.params _ hparams)) ?_
    refine Derives.seqOk _ _ _ _ _ _ _ hpsD ?_
    refine Derives.seqOk _ _ _ _ _ _ _
      (derives_tok ")" _ (noWsB_cons _ _ (by decide))) ?_
    refine Derives.seqOk _ _ _ _ _ _ _
      (derives_tok ":" _ (noWs_printTy d.retTy _)) ?_
    refine Derives.seqOk _ _ _ _ _ _ _ htyD ?_
    exact Derives.seqOk _ _ _ _ _ _ _ (derives_eqTok _ hnwBody) hbD
  · rcases hpsV with ⟨tf, htf, hnil⟩ | ⟨pT, hpT, hpsOf⟩
    · subst htf
      rw [funDefOf_decode_nil _ _ _ _ _ _ _ _ _ d.name d.retTy d.body hiV htyV hbV,
        ← hnil]
    · subst hpT
      rw [funDefOf_decode_cons _ _ _ _ _ _ _ _ _ d.name d.params d.retTy d.body
        hiV hpsOf htyV hbV]

/-! ## The FunDef* star -/

/-- Concatenated canonical text of a function list (`printFuns`, at the
`List Char` level). -/
def funsText : List FunDef → List Char
  | [] => []
  | d :: rest => (printFun d).toList ++ funsText rest

theorem printFuns_toList (ds : List FunDef) : (printFuns ds).toList = funsText ds := by
  induction ds with
  | nil => simp [printFuns, funsText]
  | cons d rest ih => simp [printFuns, funsText, String.toList_append, ih]

theorem funDef_fail_of_kwDef_fail (input : List Char)
    (h : Derives shallotGrammar (kw "def") input .fail) :
    Derives shallotGrammar (.nt NT.funDef) input .fail :=
  Derives.ntFail _ _ _ funDef_rule (Derives.seqFail₁ _ _ _ h)

/-- Non-empty function text starts with `'d'` — not whitespace, not an
operator head, and a valid expression follow. -/
theorem funsText_head_facts (d : FunDef) (rest : List FunDef) (suffix : List Char) :
    noWsB (funsText (d :: rest) ++ suffix) = true ∧
    exprFollowB (funsText (d :: rest) ++ suffix) = true := by
  have hEq : funsText (d :: rest) ++ suffix =
      (printFun d).toList ++ (funsText rest ++ suffix) := by
    simp [funsText, List.append_assoc]
  rw [hEq, printFun_toList]
  exact ⟨noWsB_cons _ _ (by decide), exprFollowB_cons _ _ (by decide)⟩

/-- The `FunDef*` star of RT-L3: the concatenated function text parses as
the star, stopping exactly at `follow` (on which `FunDef` must fail —
supplied by `kw "def"` dying on `main`'s text), and `funItems` recovers
the list. `sepListB` carries the boundary guard for the LAST body. -/
theorem derives_printFuns : ∀ (ds : List FunDef) (follow : List Char),
    ds.all printableFunB = true →
    noWsB follow = true → opFollowB follow = true →
    sepListB ds follow = true →
    Derives shallotGrammar (.nt NT.funDef) follow .fail →
    ∃ t, Derives shallotGrammar (.star (.nt NT.funDef)) (funsText ds ++ follow)
      (.ok t follow) ∧ funItems t = .ok ds := by
  intro ds
  induction ds with
  | nil =>
    intro follow _ _ _ _ hfail
    exact ⟨.starNil, Derives.starNil _ _ hfail, rfl⟩
  | cons d rest ih =>
    intro follow hall hnw hop hsep hfail
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have hEq : funsText (d :: rest) ++ follow =
        (printFun d).toList ++ (funsText rest ++ follow) := by
      simp [funsText, List.append_assoc]
    rw [hEq]
    cases rest with
    | nil =>
      have hsep' : (!bareVarB d.body || headNot '(' follow) = true := hsep
      have hbf : exprFollowB follow = true ∨
          (bareVarB d.body = false ∧ opFollowB follow = true) := by
        cases hbv : bareVarB d.body with
        | false => exact Or.inr ⟨rfl, hop⟩
        | true =>
          rw [hbv] at hsep'
          simp only [Bool.not_true, Bool.false_or] at hsep'
          exact Or.inl (exprFollowB_of_op follow hop hsep')
      obtain ⟨td, hdD, hdV⟩ := derives_printFun d follow hall.1 hnw hbf
      refine ⟨.starCons (.nodeNT NT.funDef td) .starNil, ?_, ?_⟩
      · exact Derives.starCons _ _ _ _ _ _ hdD (Derives.starNil _ _ hfail)
      · simp only [funItems, hdV]; rfl
    | cons d' rest' =>
      have hsep' : sepListB (d' :: rest') follow = true := hsep
      obtain ⟨hnwR, hefR⟩ := funsText_head_facts d' rest' follow
      obtain ⟨td, hdD, hdV⟩ := derives_printFun d (funsText (d' :: rest') ++ follow)
        hall.1 hnwR (Or.inl hefR)
      obtain ⟨ts, hsD, hsV⟩ := ih follow hall.2 hnw hop hsep' hfail
      refine ⟨.starCons (.nodeNT NT.funDef td) ts, ?_, ?_⟩
      · exact Derives.starCons _ _ _ _ _ _ hdD hsD
      · simp only [funItems, hdV, hsV]; rfl

/-! ## The Program layer (RT-L3 payoff) -/

/-- Bridge from the AST-level guard to the text-level one. -/
theorem sepListB_of_sepOkB : ∀ (ds : List FunDef) (m : Expr),
    printableB m = true → sepOkB ds m = true →
    sepListB ds ((printExpr m).toList) = true := by
  intro ds
  induction ds with
  | nil => intro m _ _; rfl
  | cons d rest ih =>
    intro m hm hsep
    cases rest with
    | nil =>
      have hsep' : (!(bareVarB d.body && parenHeadB m)) = true := hsep
      show (!bareVarB d.body || headNot '(' ((printExpr m).toList)) = true
      cases hbv : bareVarB d.body with
      | false => rfl
      | true =>
        rw [hbv] at hsep'
        simp only [Bool.true_and, Bool.not_eq_true'] at hsep'
        have hh := printExpr_headNot_paren m hm hsep' []
        rw [List.append_nil] at hh
        simp [hh]
    | cons d' rest' => exact ih m hm hsep

theorem printProgram_toList (p : Program) :
    (printProgram p).toList = funsText p.funs ++ (printExpr p.main).toList := by
  simp [printProgram, String.toList_append, printFuns_toList]

/-- **RT-L3** — the program layer of the parser roundtrip: for every
printable program, the canonical text `printProgram p` derives at
`NT.program` consuming the WHOLE input (EOF via `!.`), and `treeToAst`
recovers `p` exactly. -/
theorem derives_printProgram (p : Program) (hp : printableProgB p = true) :
    ∃ t, Derives shallotGrammar (.nt NT.program) (printProgram p).toList
      (.ok (.nodeNT NT.program t) []) ∧ treeToAst t = .ok p := by
  simp only [printableProgB, Bool.and_eq_true] at hp
  obtain ⟨⟨hfuns, hmain⟩, hsep⟩ := hp
  have hopM : opFollowB ((printExpr p.main).toList) = true := by
    have hh := (printExpr_head p.main hmain []).1
    rwa [List.append_nil] at hh
  have hkwDef : Derives shallotGrammar (kw "def") ((printExpr p.main).toList) .fail := by
    have hh := (printExpr_head p.main hmain []).2
    rwa [List.append_nil] at hh
  have hnwM : noWsB ((printExpr p.main).toList) = true := by
    have hh := (printExpr_text p.main hmain []).1
    rwa [List.append_nil] at hh
  obtain ⟨tm, hmD, hmV⟩ := derives_printExpr p.main [] hmain rfl rfl
  rw [List.append_nil] at hmD
  obtain ⟨ts, hsD, hsV⟩ := derives_printFuns p.funs ((printExpr p.main).toList)
    hfuns hnwM hopM (sepListB_of_sepOkB p.funs p.main hmain hsep)
    (funDef_fail_of_kwDef_fail _ hkwDef)
  have hnwAll : noWsB (funsText p.funs ++ (printExpr p.main).toList) = true := by
    cases p.funs with
    | nil => simpa [funsText] using hnwM
    | cons d rest => exact (funsText_head_facts d rest _).1
  rw [printProgram_toList]
  refine ⟨.seq spaceTreeNil (.seq ts (.seq (.nodeNT NT.expr tm) .notT)), ?_, ?_⟩
  · apply Derives.ntOk _ _ _ _ _ program_rule
    refine Derives.seqOk _ _ _ _ _ _ _ (derives_spacing_nil _ hnwAll) ?_
    refine Derives.seqOk _ _ _ _ _ _ _ hsD ?_
    exact Derives.seqOk _ _ _ _ _ _ _ hmD (Derives.notFail _ _ Derives.anyFail)
  · simp only [treeToAst, hsV, hmV]; rfl

/-! ## Parser connection (T3 + T0) -/

/-- The verified interpreter parses canonical program text back to the
program, for every sufficiently large fuel: T3 (`pegRun_complete`) turns
the RT-L3 derivation into an interpreter run, T0 (`pegRun_mono_le`) lifts
it to all larger fuels, and `parseShallot` unwraps the start-symbol node
into `treeToAst`. -/
theorem parse_print (p : Program) (hp : printableProgB p = true) :
    ∃ fuel, ∀ fuel', fuel ≤ fuel' → parseShallot fuel' (printProgram p) = .ok p := by
  obtain ⟨t, hd, hast⟩ := derives_printProgram p hp
  obtain ⟨f, hf⟩ := pegRun_complete hd
  refine ⟨f, fun f' hle => ?_⟩
  have hrun : pegRun shallotGrammar f' (.nt NT.program) (printProgram p).toList =
      some (.ok (.nodeNT NT.program t) []) := pegRun_mono_le hle hf
  unfold parseShallot
  rw [hrun]
  exact hast

/-- Simple existential corollary of `parse_print`. -/
theorem parse_print_exists (p : Program) (hp : printableProgB p = true) :
    ∃ fuel, parseShallot fuel (printProgram p) = .ok p := by
  obtain ⟨f, hf⟩ := parse_print p hp
  exact ⟨f, hf f (Nat.le_refl f)⟩

/-! ## The pipeline theorem — the project's closing composition

Every verified layer in one statement: the canonical text of `p` parses
back to exactly `p` through the verified PEG interpreter (RT-L3 + T3 +
T0), acceptance by the verified typechecker gives well-typedness (V-TC),
the interpreter's value is type-correct (type soundness), and the
compiled VM computes the SAME value (V2). -/
theorem pipeline_correct (p : Program) (τ : Ty) (v : Value) (fuel : Nat)
    (hp : printableProgB p = true)
    (hc : checkProgram p = .ok τ)
    (hr : runProgram p fuel = some (.ok v)) :
    ∃ pf, (∀ pf', pf ≤ pf' → parseShallot pf' (printProgram p) = .ok p) ∧
      WTProg p ∧ ValHasTy v τ ∧ ∃ vmf, vmRunProgram p vmf = some (.ok v) := by
  obtain ⟨pf, hparse⟩ := parse_print p hp
  have hwt : WTProg p := checkProgram_sound p τ hc
  have hty : ValHasTy v τ := by
    rcases runProgram_sound hc hr with hdiv | ⟨v', hv', htyv⟩
    · exact absurd hdiv (by simp)
    · injection hv' with hvv
      rw [hvv]
      exact htyv
  exact ⟨pf, hparse, hwt, hty, compile_correct hr⟩

#print axioms derives_printProgram
#print axioms parse_print
#print axioms pipeline_correct

end Shallot
