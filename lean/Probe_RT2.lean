import Shallot.Syntax.Lexemes

set_option autoImplicit false

namespace Shallot

example (tn : PTree) (k : Int) (h : numberVal tn = .ok k) :
    primaryOf (.choiceL (.nodeNT NT.number tn)) = .ok (.intLit k) := by
  simp only [primaryOf, h]; rfl

example (t : PTree) (e : Expr) (h : unaryOf t = .ok e) :
    mulOf (.seq (.nodeNT NT.unary t) .starNil) = .ok e := by
  simp only [mulOf, h]; rfl

example (tA tB : PTree) (l r' : Expr) (opT : PTree)
    (hA : mulOf tA = .ok l) (hB : mulOf tB = .ok r') :
    addOf (.seq (.nodeNT NT.mulE tA)
      (.starCons (.seq (.choiceL opT) (.nodeNT NT.mulE tB)) .starNil)) =
      .ok (.binop .add l r') := by
  simp only [addOf, hA, goAdd, hB]; rfl

example (c : Char) (h : isDigitB c = true) : isWsB c = false := by
  unfold isDigitB leChar at h
  unfold isWsB beqChar
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  have e0 : '0'.toNat = 48 := rfl
  have e9 : '9'.toNat = 57 := rfl
  have eSp : ' '.toNat = 32 := rfl
  have eNl : '\n'.toNat = 10 := rfl
  have eTb : '\t'.toNat = 9 := rfl
  have eCr : '\r'.toNat = 13 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

example (c : Char) (h : isIdStartB c = true) : isDigitB c = false := by
  unfold isIdStartB beqChar at h
  unfold isDigitB leChar at h ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at h
  simp only [Bool.and_eq_false_iff, Nat.ble_eq_false]
  have : 'a'.toNat = 97 := rfl
  have : 'z'.toNat = 122 := rfl
  have : 'A'.toNat = 65 := rfl
  have : 'Z'.toNat = 90 := rfl
  have : '_'.toNat = 95 := rfl
  have : '0'.toNat = 48 := rfl
  have : '9'.toNat = 57 := rfl
  omega

-- kw derivation defeq on literal input
example (r : List Char) (h : noWsB r = true) :
    Derives shallotGrammar (kw "true") ('t' :: 'r' :: 'u' :: 'e' :: ' ' :: r)
      (.ok (kwTree "true") r) :=
  derives_kw "true" r h

-- ident on cons-form input
example (x : String) (r : List Char) (c : Char) (cs : List Char)
    (hx : validIdentB x = true) (hr : noWsB r = true) (hxl : x.toList = c :: cs) :
    ∃ t, Derives shallotGrammar (.nt NT.ident) (c :: (cs ++ ' ' :: r))
        (.ok (.nodeNT NT.ident t) r) ∧ identName t = .ok x := by
  have := derives_ident x r hx hr
  rw [hxl] at this
  exact this

end Shallot
