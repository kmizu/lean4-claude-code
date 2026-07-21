# 5. Lens 抽出器 — 証明された Lean コードを Scala 3 にする

[English](../en/05-lens.html) | **日本語** ｜ [← 4章](04-shallot.html) ｜ [目次](../index.html) ｜ [6章 →](06-reading-guide.html)

証明は Lean の中で完結しました。しかし証明されたパーサを JVM のプロダクトで
使いたければ、Lean の外に持ち出す必要があります。Lens は Shallot の実行可能
部分を Scala 3 に変換する自作の抽出器です。Coq → OCaml の extraction は有名
ですが、**Lean → Scala/JVM の抽出器は先行事例が見つかりませんでした**。
この章はその仕組みと、「どこまで信じられるのか」の正直な線引きの話です。

## 5.1 なぜ自明でないのか

「Lean の関数定義を構文変換すればいいだけでは？」と思うかもしれません。
問題は、Lean が保存しているのは**あなたが書いたコードではない**ことです。
パーサ屋向けの類推で言えば：ソースを印字し直すのではなく、**コンパイル済みの
中間表現から元のコードを復元する**作業に近い。

具体的には、Lean の再帰関数は elaboration（脱糖・型推論）を経ると、
パターンマッチは補助関数（matcher）に、構造的再帰は `brecOn` という
再帰子に、整礎再帰は `WellFounded.fix` という不動点コンビネータに
姿を変えます。そこから可読な再帰関数を逆コンパイルするのは骨の折れる仕事です。

## 5.2 等式補題ルート

Lens の解法は、Lean コンパイラ内部 API の **等式補題（equation lemmas）** を
使うことです（`lean/Lens/Equations.lean` のヘッダから）：

> `Lean.Meta.getEqnsFor?` returns, for structural/well-founded recursion AND
> top-level pattern-matching definitions, one theorem per source alternative
> of the form `∀ vars, f p₁ … pₙ = rhs` — crucially with **direct** recursive
> calls in the RHS (no `brecOn`/`WellFounded.fix` decompilation needed).

つまり Lean 自身が「この関数はこのパターンのときこの右辺に等しい」という
定理群を、**再帰呼び出しが直接呼び出しの形のまま**提供してくれる。抽出器は
その等式の左辺からパターンを、右辺から本体を読み取って Scala の `match` を
再構成します。`brecOn` の逆コンパイルは丸ごと不要になります。

before / after を見てください。Lean 側（`lean/Shallot/Demo.lean`）：

```lean
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def gcd (a b : Nat) : Nat :=
  if a = 0 then b else gcd (b % a) a
termination_by a
```

生成された Scala（`scala/generated/.../Shallot.scala`、一字一句このまま）：

```scala
def fib(x0: BigInt): BigInt =
  (x0 match {
    case _g0 if _g0 == BigInt(0) => BigInt(0)
    case _g0 if _g0 == BigInt(1) => BigInt(1)
    case _g0 if _g0 >= 2 => { val n = _g0 - 2; (fib((n + BigInt(1))) + fib(n)) }
  })

@annotation.tailrec
def gcd(a: BigInt, b: BigInt): BigInt =
  (if (a == BigInt(0)) then b else gcd(RT.natMod(b, a), a))
```

`n + 2` のようなペアノ数のパターンはガード付き case（`_g0 >= 2` と
`val n = _g0 - 2`）に落ち、整礎再帰の gcd は**直接再帰**のまま出てきて、
おまけに末尾再帰検出が `@annotation.tailrec` を付けています（Scala コンパイラが
この注釈を検証するので、検出が間違っていればコンパイルが落ちる——ここでも
fail-loud です）。

## 5.3 手監査の領域：Builtins

`Nat` を `BigInt` に対応させる、と言うのは簡単ですが、意味論の細部に地雷が
あります。`lean/Lens/Builtins.lean` のヘッダより：

> Maps a *minimal* whitelist of Lean core constants onto Scala equivalents.
> - `Nat` subtraction truncates; `Nat`/`Int` division/modulo by zero = 0 / identity
> - `Int` default `/`, `%` are **Euclidean** (`ediv`/`emod`) — remainder is
>   always non-negative. Scala `BigInt` `/`/`%` are T-division, so these go
>   through `RT.intDiv`/`RT.intMod`.

Lean の `Nat` の引き算は 0 で切り詰め（`3 - 5 = 0`）、ゼロ除算は 0、そして
Lean の `Int` の `/`・`%` は**ユークリッド除算**（余りが常に非負。
`(-7) / 2 = -4`）です。Scala の `BigInt` は T 除算（`-7 / 2 = -3`）なので、
そのまま `/` に写すと**証明が正しくてもプログラムが間違う**。こうした対応は
ホワイトリスト形式の小さな表に隔離され、実測（Lean の `#eval` との突き合わせ）で
ピン留めされています。この表が、人間が読んで監査すべき領域です。

## 5.4 TCB — どこまでが証明で、どこからが信頼か

はっきり書きます。**抽出器は検証されていません。** 定理が保証するのは
Lean の中の意味論で、生成された Scala が正しい保証は、論理的には
ありません。信頼すべきもの（Trusted Computing Base）は：

- Lean のカーネル（証明の検査者）
- **Lens 抽出器そのもの**
- 手書きの Scala ランタイム（`shallot.rt`、約 550 行——上の `RT.intDiv` など）
- Scala コンパイラと JVM

CompCert（検証済み C コンパイラ）ですら printer や assembler は TCB です。
検証プロジェクトの誠実さは「全部証明した」と言うことではなく、**証明した
範囲と信頼した範囲の線を明示する**ことにあります。

## 5.5 それでも橋を架ける：差分ハーネス

論理的な保証がない部分には、経験的な検査を最大化して当てます。仕掛けの
核は、**テストケースの表そのものを Lean で 1 回だけ定義して、抽出する**ことです
（`lean/Shallot/Corpus.lean`）：

```lean
def cases : List (String × String) :=
  [ ("000-nat-sub-underflow", renderNat (clampSub 3 5)),
    ("004-bigint-fact25",     renderNat (fact 25)),
    ("006-fib-20",            renderNat (fib 20)),
    ...
```

Lean 側のランナーはこの表を**ネイティブに**評価し、Scala 側の CLI は
**抽出された同じ表**を評価します。それぞれの出力（60 ケースの JSONL）を
突き合わせる：

```json
{"case":"000-nat-sub-underflow","phase":"eval","status":"ok","result":"0"}
{"case":"004-bigint-fact25","phase":"eval","status":"ok","result":"15511210043330985984000000"}
{"case":"006-fib-20","phase":"eval","status":"ok","result":"6765"}
```

ケース定義が单一ソースなので、「Lean 側とテーブルがズレていた」という
差分テストあるあるが起きません。結果の文字列化すら Lean で書いたレンダラを
抽出して共有しているので、**レンダラのバグも抽出器のバグも、すべて diff に
現れます**。実際、開発中に敵対的レビューで見つかった抽出器の変数捕獲バグ
（Lean で 42 を返す関数が Scala で 0 を返す、という筋の悪いやつ）は、
再現ケースごと corpus に永久保存され、回帰を監視し続けています。

## この章の持ち帰り

**「証明済み」の保証は抽出境界で止まる。だから境界を明示し、境界の両側で
同一の定義を実行して突き合わせる。** 保証の切れ目を隠さないことと、切れ目に
最強の経験的検査を当てること——このふたつが揃って、初めて「検証済み◯◯を
実用言語に持ち出した」と胸を張れます。

---

[← 4章 Shallot 言語](04-shallot.html) ｜ [目次](../index.html) ｜ [6章 読みどころガイド →](06-reading-guide.html)
