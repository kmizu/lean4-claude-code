# 4. Shallot 言語 — 型検査器・インタプリタ・コンパイラの証明スタック

[English](../en/04-shallot.html) | **日本語** ｜ [← 3章](03-peg-semantics.html) ｜ [目次](../index.html) ｜ [5章 →](05-lens.html)

3 章の PEG フレームワークは汎用品でした。この章では、それを使って定義した
小さな言語 **Shallot** の上に、型検査器・インタプリタ・コンパイラの証明が
どう積み上がっているかを見ます。最後に、roundtrip 証明が**実在する文法の穴**を
掘り当てた話——本連載のクライマックス——をやります。

## 4.1 言語 15 秒ツアー

Shallot は int と bool だけを持つ第一階の関数型言語です。具象構文はこんな感じ
（`examples/fact.shl`）：

```
def fact ( n : int ) : int = if n <= 0 then 1 else n * fact ( n - 1 )
fact ( 10 )
```

文法は**データ**として定義されています。3 章の `PExp` の値を組み立てるだけです
（`lean/Shallot/Syntax/Grammar.lean`）：

```lean
/-- Keyword: literal + not-followed-by-identifier-char + spacing. -/
def kw (s : String) : PExp :=
  .seq (.lit s.toList) (.seq (.notP idContP) (.nt NT.spacing))

/-- `'=' !'='` then spacing (assignment, not equality). -/
def eqTok : PExp := .seq (.chr '=') (.seq (.notP (.chr '=')) (.nt NT.spacing))

/-- Left-associative operator tier: `Sub (op Sub)*`. -/
def tier (sub : Nat) (ops : PExp) : PExp :=
  .seq (.nt sub) (.star (.seq ops (.nt sub)))
```

`kw` はキーワードの直後に識別子文字が続かないことを否定先読みで保証する
（`if` と `iffy` の区別）、`eqTok` は `=` と `==` の衝突を `!'='` で回避する——
PEG 使いにはお馴染みのイディオムがそのまま値になっています。そして
**パーサはこの文法値を 3 章の検証済み `pegRun` に食わせるだけ**なので、
健全性・完全性・決定性の定理が Shallot のパーサに自動的に適用されます。

## 4.2 型検査器：健全「かつ」完全

型システムは 2 層で定義されます。**仕様**は帰納的述語 `HasType`（推論規則、
3 章の読み方そのまま）、**実装**は `Except` を返す再帰関数 `typecheck`。
そして両者の一致が両方向で証明されています：

```lean
-- L1 健全性: 検査器が ok と言ったら、型付け関係が本当に成り立つ
theorem typecheck_sound : typecheck S Γ e = .ok τ → HasType S Γ e τ

-- L2 完全性: 型付け関係が成り立つなら、検査器は必ず ok と言う
theorem typecheck_complete : HasType S Γ e τ → typecheck S Γ e = .ok τ
```

健全性だけなら「検査器が慎重すぎる」余地が残ります（正しいプログラムを
弾いても健全性は破れない）。完全性が加わって初めて「検査器は仕様と過不足なく
一致する」と言えます。実装バグでうっかり厳しくしても緩くしても、どちらかの
定理が壊れて検出される——仕様と実装を別々に書いて両方向で縫い合わせる、
この形が検証の基本パターンです。

## 4.3 型健全性：「実行時型エラー」の不在証明

インタプリタは 3 値規約（成功／意味論的エラー／燃料切れ）の燃料付き評価器です。
エラーには `stuckType`（型の合わない演算）や `stuckUnbound`（未束縛変数）などの
「stuck 系」と、`divByZero` があります。型健全性はこう述べられます
（`lean/Shallot/Lang/TypeSound.lean`）：

```lean
/-- **L5** — TYPE SOUNDNESS. A well-typed expression of a well-typed
program cannot get stuck: every defined interpreter outcome is either the
allowed `divByZero` error or a value of the expression's static type. -/
theorem eval_sound
    (hwt : WTProg p) (ht : HasType (p.funs.map FunDef.sig) Γ e τ)
    (henv : EnvTy env Γ) (h : eval (mkFunTable p.funs) fuel env e = some r) :
    (∃ er, r = .error er ∧ okErr er) ∨ (∃ v, r = .ok v ∧ ValHasTy v τ)
```

日本語にすると：「型の付いたプログラムの評価結果は、divByZero か、
**静的な型どおりの値**か、どちらかしかない」。stuck 系エラーはひとつも
出てこない——出てこないことが**定理**です。テストで「エラーが出なかった」の
ではなく、「エラーになる実行が存在し得ない」。型システムの存在意義を
1 本の主張に圧縮した、PL 理論の古典がここに実装されています。

## 4.4 コンパイラの正しさ

Shallot にはスタック VM へのコンパイラもあります。コンパイラ本体は素直です
（`lean/Shallot/Vm/Compile.lean`、抜粋）：

```lean
mutual
  def compileExpr (σ : List String) : Expr → List Instr
    | .intLit n => [.pushI n]
    | .var x =>
      match idxOf σ x with
      | some i => [.load i]
      | none => [.crash]
    | .binop op l r => compileExpr σ l ++ compileExpr σ r ++ [.binop op]
    | .ite c t e =>
      compileExpr σ c ++ [.branch (compileExpr σ t) (compileExpr σ e)]
    | .letE x bound body =>
      compileExpr σ bound ++ [.bind] ++ compileExpr (x :: σ) body ++ [.unbind]
    | .call f args => compileArgs σ args ++ [.call f (countArgs args)]
  ...
end
```

正しさの主張はこの上なくシンプルです（`lean/Shallot/Vm/Correct.lean`）：

```lean
/-- **V2** — whole-program compiler correctness: if the interpreter runs
the program to a value, the compiled program runs to the SAME value. -/
theorem compile_correct (h : runProgram p fuel = some (.ok v)) :
    ∃ fuel', vmRunProgram p fuel' = some (.ok v)
```

「インタプリタで値 v になったプログラムは、コンパイルして VM で走らせても
同じ v になる」。証明の心臓部は**前進シミュレーション**で、コンパイル時の
変数環境 σ と実行時のローカル領域が添字単位で対応することを不変条件として
式の構造に沿って回します。

証明工学的に面白いのは、シミュレーション補題が**継続渡し形式**（CPS）で
立てられていることです：

```lean
theorem compile_sim_cont ... :
    eval (mkFunTable funs) f env e = some (.ok v) →
    EnvMatch env σ locals →
    vmRun (mkCodeTable funs) fr rest (v :: stack) locals = some (.ok out) →
    ∃ f', vmRun (mkCodeTable funs) f' (compileExpr σ e ++ rest) stack locals
      = some (.ok out)
```

「e のコードの**後ろに続くコード rest** が、結果の値を積んだスタックから
最終結果 out に到達するなら、`compileExpr σ e ++ rest` 全体も同じ out に到達する」。
なぜこの回りくどい形か。素朴な「コードの連接は実行の連接」補題は、実は
**成り立ちません**——`bind`/`unbind` 命令がローカル領域を書き換えるため、
前半実行後のローカルの姿を後半に引き渡す情報が足りないのです。証明を書いた
エージェントはこの反例（`c₁ = [bind]`）を発見し、CPS 形に組み替えました。
継続は**同じローカル**で走る——なぜならコンパイラの出力は bind/unbind が
必ず対になっているから。コンパイラの規律が証明の形を決めた好例です。

## 4.5 roundtrip、そして仕様の穴が見つかった話

最後のピースは **roundtrip**：「AST を正準形で印字し、検証済みパーサで
読み戻すと、元の AST に戻る」。印字は全トークン後置 1 スペース・複合式は
全括弧という機械的な正準形です。定理はこう述べられます
（`lean/Shallot/Syntax/Roundtrip.lean`）：

```lean
theorem parse_print (p : Program) (hp : printableProgB p = true) :
    ∃ fuel, ∀ fuel', fuel ≤ fuel' → parseShallot fuel' (printProgram p) = .ok p
```

仮定 `printableProgB` は「正準印字可能なプログラム」の特徴付けで、識別子が
有効（キーワードでない等）といった条件が入ります。ここまでは想定内。
ところが証明の途中で、この仮定に**もう 1 つ条件を足さないと定理が偽になる**
ことが判明しました。ファイルの冒頭コメントから引用します：

> when the LAST function's body is a bare variable and `main`'s canonical
> text starts with `'('`, the PEG's prioritized `Call / Ident` choice
> extends the body across the boundary (`… = x ( 1 + 2 ) ` parses
> `x ( 1 + 2 )` as a call, and the program parse then FAILS at EOF).
> Checked empirically:
> `parseShallot _ "def f ( ) : int = x ( 1 + 2 ) " = .error .syntaxErr`.

つまり：最後の関数の本体が**裸の変数** `x` で、続く main 式が `(` で始まると、
`x` と `( 1 + 2 )` のあいだの**関数境界を越えて** `x ( 1 + 2 )` が関数呼び出しに
見えてしまう。PEG の優先選択 `Call / Ident` は貪欲に Call を先に試すからです。
呼び出しとして読んだ結果、プログラム全体の解析は EOF で破綻します。

この形は well-typed でも作れます（`def id ( a : int ) : int = a` に括弧付き main）。
そして本プロジェクトの**60 ケースの差分テストは一度もこの形を踏んでいません
でした**。見つけたのはテストではなく、証明です——roundtrip の帰納法がこの
ケースで通らず、通らない理由を掘ったら実パーサで再現する反例が出てきた。
対処として仮定に分離ガードが 1 条件加わりました：

```lean
/-- The separation guard: the LAST function's body must not be a bare
variable when `main` prints `'('`-headed. -/
def sepOkB : List FunDef → Expr → Bool
  | [], _ => true
  | [d], m => !(bareVarB d.body && parenHeadB m)
  | _ :: ds, m => sepOkB ds m
```

ガードは証明の都合の弱体化ではなく、**印字器と文法の境界に実在する条件の
正確な特徴付け**です（他のすべての境界が安全であることは、逆に証明が保証して
います）。「形式検証は仕様の穴を見つける」とはよく言われますが、それが
PEG の優先選択という、この読者層にいちばん馴染み深い機構で起きた、
というのが本プロジェクト随一の収穫でした。

## 4.6 全部を 1 本に：pipeline_correct

締めの定理は、ここまでの全レイヤの合成です：

```lean
theorem pipeline_correct (p : Program) (τ : Ty) (v : Value) (fuel : Nat)
    (hp : printableProgB p = true)
    (hc : checkProgram p = .ok τ)
    (hr : runProgram p fuel = some (.ok v)) :
    ∃ pf, (∀ pf', pf ≤ pf' → parseShallot pf' (printProgram p) = .ok p) ∧
      WTProg p ∧ ValHasTy v τ ∧ ∃ vmf, vmRunProgram p vmf = some (.ok v)
```

正準印字したテキストは検証済みパーサで**ちょうど p** に戻り、p は型付け関係の
意味で well-typed で、評価結果 v は静的な型 τ に適合し、コンパイルした VM も
**同じ v** を計算する。パーサ・型検査器・インタプリタ・コンパイラ、それぞれの
定理が 1 本の合成定理に流れ込む——「完全な仕様とそれを満たすプログラムと証明の
セット」の、これが最終形です。

## この章の持ち帰り

**証明が行き詰まった場所こそが、仕様のバグの在り処だった。** roundtrip の
帰納法が通らない 1 ケースを掘ったら、60 の差分テストが見逃した PEG の
境界条件が出てきました。検証は合格印を押す作業ではなく、仕様と実装の
食い違いを網羅的に探索する装置なのです。

---

[← 3章 PEG の形式意味論](03-peg-semantics.html) ｜ [目次](../index.html) ｜ [5章 Lens 抽出器 →](05-lens.html)
