# ReBeL ロードマップ

## 方針と完了条件

この計画は本 fork の具体的な研究計画であり、既存証明の完成宣言ではありません。過去のチャットにあった「CFR はほぼ完成」「少し拡張だけで十分」という評価を確定事項として引き継ぎません。

最終対象は本文 Sections 1–9、補遺 A–J、Theorems 1–5、Lemmas 1–3、Algorithms 1–2、番号付き式と証明中の主張、公式公開実装の ReBeL 関連動作です。導入・関連研究・結論は主張の所在と適用範囲を追跡し、比較対象の全研究を自動的に別プロジェクトとして再形式化するわけではありません。外部定理を証明に使えば、その依存の証明責任は残ります。

`coverage.json` は原典の親義務と内容ハッシュ付き子台帳を保持します。M01-B で番号付き式、脚注、擬似コードの各操作、公式実装の関数・設定の所在を追加しました。`check_coverage.py --expanded-json` で全項目を読めます。行数を分母にした「完成率」を使わないでください。

各証明の完了には、原文の位置、完全な Lean declaration、前提の対照表、対象 commit、ビルド結果、公理依存、非自明な正例/負例、意味的レビューを必要とします。`verified`、`qualified`、`refuted`、`empirical_documented` は別状態です。原文を反証して修正版を証明した場合も、元の主張を証明したと数えません。未解決の実装保証や条件付き oracle を残して「ReBeL 全体を無条件に検証済み」と報告しません。

## 設計の原則

既存 `ExecutionProtocol`、`InformationModel`、`FinDist`、canonical Nash/utility/deviation、counterfactual reach を再利用します。新コードの候補配置は `GameTheory/ReBeL/`、公開 namespace は `GameTheory.ReBeL` です。一般数学を抽出する際は既存 `GameTheory.Math` の依存制約を維持し、解析の依存を基本実行意味論へ逆流させません。既存 `GameTheory.lean` に巨大な ReBeL import を無条件に追加しません。

まず有限・有限ホライズン・二人零和・完全記憶の明示的な定理を実装します。無限 carrier や一般ホライズンを必要とする主張は、この限定定理の完了で閉じず、対象域の拡張を別行として残します。ゲームの長さと学習回数の無限極限を混同しません。

仕様層は実数と有限支持分布、実行層は明示的列挙とまず有理数を使います。後に浮動小数点・学習ネットワーク・並列実行を接続します。実行層に `Classical.choose` や隠れた実数等値判定を持ち込まないでください。

## 最初に監査する危険点

### R1: PBS の意味

本文 §4 は joint distribution とプレイヤーごとの分布表現を併用しています。**周辺分布を並べただけでは一般の相関を復元できません。** public-history fiber 上の `FinDist` を参照意味論の候補にし、chance の相関・カードの重複禁止・支持条件を保った表現を作ります。player reach-factor 表現との橋渡しは別定理です。任意の周辺分布の直積で済ませないこと。

### R2: 情報と条件付き確率

既存 `InfoState` は圧縮可能なので、論文の action-observation history と同一とは限りません。完全記憶、public trace の復元、同じ情報集合の同じ合法手、ゼロ到達確率、実到達と反事実到達、偶然の相関を検証します。`bayesBelief` は個人の information fiber 上の posterior であり、PBS そのものではありません。

### R3: Theorem 1 の拡張と supergradient

補遺 F の正規化拡張について、simplex 上の supporting hyperplane と、非正規化領域全体の concave supergradient と、局所的な微分概念を分離します。正規化は凹性を一般には保存しません。

監査用の有理数例: `f(x,y)=x/(x+y)`、`b=(1/2,1/2)`、中心化勾配 `g=(1/2,-1/2)`、`z=(1/2,3/2)`。`f(z)=1/4` ですが `f(b)+g·(z-b)=0` です。したがってこの g を正の領域全体の supporting supergradient と解釈する不等式は成立しません。この有理数診断と正例・境界例は **M01-A で Lean 証明済みですが、元の Theorem 1 の全解釈を反証したとの宣言ではありません**。元ゲームへの埋め込みと、原文が意図する拡張/微分概念を監査してください。

Lemma 1 の「相手固定なら線形」も、同じ相手条件付き分布の下で私的状態ごとの最適応答を一つの合法な戦略へ組み立てられることまで示します。単に expectation の線形性を呼ぶだけでは済ませません。supergradient の平均には凸結合の係数条件を明記します。

### R4: 学習の量化

Theorem 2 は理想化した記憶器を扱います。学習回数 N、探索反復数 T、ゲーム深さを別変数にし、確率 1 の主張か、期待値か、決定論的 fairness 条件付きかを分けます。連続 PBS 空間の「全点を無限回訪問」を仮定しません。アルゴリズムが生成する query 集合、更新が安定した後の正の sampling probability、tie-break の決定性、必要な可測性を証明します。無限 sampling の確率法則が必要なら有限ゲーム用 FinDist と別の Mathlib measure-theory 層を明示的に接続します。

### R5: 定理文と証明の不一致候補

補遺 G の Theorem 2 再掲は equilibrium policy の value との対応として書かれ、本文は error として述べます。基準値とノルムを固定します。出版本文p8、補遺p21の Theorem 3 再掲とp22の証明末尾には `delta*C1 + delta*C2/sqrt(T)` が印刷されていますが、基底ケースは有限反復誤差 `k1/sqrt(T)` を残します。M01-B で arXiv v2・引用先と照合し、独立な前提付き漸化式から `A_d*delta+B_d/sqrt(T)` を導く代数診断を記録しました。solver がその漸化式を満たす証明は M06 の義務です。推測で原文を修正して同じ定理名で通さないこと。

### R6: アルゴリズム変種と乱数

vanilla CFR-D、linear/discounted 系、CFR-AVG、modified CFR-AVG、FLOP、warm start を別定義にします。Theorem 5 の正確な continuation solve と実験の差分 leaf-value 更新は同一ではありません。modified 版の一般保証は証明探索と反例探索の両方を行い、文献で未解決とされたことだけを理由に放棄しません。解けていなければ未解決と記録します。

単純な局所平均と own-reach 加重平均を区別します。全体で一度選ぶ iteration、各手で引き直す iteration、共有乱数、各プレイヤーの私的乱数を区別し、相手が観測できる情報と deviation の範囲を固定します。

### R7: 既存定理の適用条件

`CounterfactualRegretMatching` は局所 theorem であり、`CounterfactualRootRegret` は supplied decomposition 等を要求します。一般ゲームの全情報集合の scheduler、同一の play trace、counterfactual payoff 実現、全 deviation に一様な評価を自分で供給する必要があります。`...Test.lean` の具体例を一般定理として数えないこと。

## 段階別ロードマップ

### M00 — 準備（今回）

原典/commit 固定、範囲とリスク、対応台帳、継続手順を追加します。既存 Lean・Lake・workflow・依存は変更しません。受入条件は fork 限定の変更と台帳構造検査であり、Lean の基底ビルドは M01 に残します。

### M01 — 実行経路と原典監査

**実施順序は M01-A（baseline・compiler loop・診断）完了後に M01-B（原典 inventory・前提監査）。**
対象SHAと統合ゲートは `STATUS.md`、段階別の記録は `M01-A.md` と `M01-B.md`。

**依存: M00。** fork の Actions 有効化を確認し、開始 commit の `lake build` と既存 architecture audits の結果を取得します。新規の最小 compiler probe で「編集→push→対象 SHA のコンパイル→ログ読取→修正」を一巡させます。必要な場合だけ fork 内へ軽量な ReBeL CI を追加し、read-only token・固定 action SHA・timeout・concurrency を使います。管理権限や workflow 有効化が不可ならユーザー操作が必要な箇所を明示します。

本文/補遺を定義・番号付き式・定理・補題・擬似コード操作に分解し、coverage の子行を追加します。PDF の版/ハッシュ、原典と解釈の差、R1–R7 を記録します。既存 Lean の候補定理は signature と仮定を確認し、原典の量化に代入できるまで未検証にします。新規 public root は最初の意味ある検証に合わせて作成します。

**受入:** baseline ログと対象 SHA、再現可能な compiler loop、全原典項目の inventory、R3/R5 の初期診断、推移的公理監査の実行方法。lint 対象も確認します。単なる空 import のビルドを ReBeL の完成に数えません。

### M02 — 有限ゲーム/情報意味論と縦断例

**依存: M01。** public action-observation history と private AOH、history fiber、reward の累積、有限性/停止証明、perfect recall を既存 Protocol に接続します。同時手番を消さず、chance を隠れたプレイヤーとして誤モデル化しません。

二段階の隠れた type のゲームを作り、同じ周辺分布で違う相関、off-path の後続意思決定、情報漏洩、同じ状態に合流する違う履歴を試します。小さな Liar's Dice 規則も早期に接続して表現を試します。

**受入:** 隠れた状態へアクセスしない戦略の型、public trace と AOH の関係、合法手/ゼロ和/停止の証明、非自明な正例/負例。定義の数ではなく downstream payoff を評価して設計を決めます。

### M03 — PBS と表現間の対応

**依存: M02。** 支持条件付き joint history law、public conditioning、Bayes update、零確率の分岐、PBS-rooted continuation を定義します。正規化されない reach weight と確率分布を別型にし、互換性付きの compact encoding と参照意味論の同値性を証明します。

belief representation と元ゲームについて、合法な戦略写像、outcome law、期待報酬、単独 deviation の保存を順に証明します。単なる結果分布の一致を equilibrium の保存と呼ばないでください。

**受入:** 更新と実行の可換性、カード/相関の反例が通ること、正確な対象域での strategic-equivalence theorem、完全情報での退化例。

### M04 — 全ゲーム CFR と実行可能な基準 solver

**依存: M02。M03 と並行可能。** 既存 reach/regret/matching を利用しつつ、全情報集合の有限 scheduler、反事実報酬の実現、root regret 分解を具体的に供給します。own-reach 加重の戦略平均と mixed/behavioral の realization equivalence を証明し、zero-sum Nash への橋渡しを作ります。

有理数の小ゲーム用実行 solver と abstract step の refinement、brute-force best response による検算を用意します。更新順、0 番目 iteration、T=0/1、regret 総和ゼロ時の fallback を固定します。

**受入:** 任意の対象有限ゲームで使える solver theorem、前提を実際に満たす二段階具体例、全 deviation への一様な finite-T bound、独立検算。既存局所定理の再命名では不可。

### M05 — Value/幾何と Theorem 1

**依存: M03。M04/M06 の完成を待たず並行可能。** PBS value、Eq.(1) の infostate best-response value、Lemmas 1/2、minimax と existence を接続します。own belief と opponent belief の変数域、境界での未到達 type、equilibrium の非一意性を扱います。

R3 を解消してから supergradient の statement を確定します。原文の広すぎる解釈が偽なら Lean 反例と修正版の別定理を作ります。最初に simplex 上の supporting inequality を証明し、必要な extension/differential の主張を分離する方針を優先して比較します。

**受入:** 原文/採用解釈/修正版の対応、型付き前提、非微分点と境界例、公理監査、Theorem 1 のどの命題を証明したのか明確な記録。

### M06 — 深さ制限 CFR-D と test-time safety

**依存: M03 + M04。M05 は自動的な必須依存にしない。** public frontier、終了済み leaf と cut leaf、continuation oracle、iteration ごとの PBS/value 更新を定義します。oracle の誤差だけでなく、返す value vector の continuation-policy との整合性を仕様化します。

exact oracle から approximate oracle へ誤差を伝播させ、深さ・payoff 範囲・情報集合数に依存する明示的な bound を導きます。random-iteration play と信念を引き継ぐ実行をモデル化し、未知の相手に対する unilateral guarantee と全体の epsilon-Nash を区別して Theorem 3 を構成します。

**受入:** depth-limited solver が抽象 full-game continuation と接続すること、誤差ゼロでも有限 T の誤差を落とさないこと、seed/平均の取り違えを検出する負例、R5 の対応記録。Theorem 3 は学習器の収束証明を前提にせず、独立に検証する。

### M07 — 再帰的自己対戦と Theorem 2

**依存: M06。** Algorithms 1/2 の状態機械、SAMPLELEAF、探索対象プレイヤー選択、探索率、反復 sampling weight、value/policy target、理想化した最新サンプル記憶器を定義します。vanilla と linear の重み・warm-start offset を別々に監査します。

まず deterministic recursive solve を証明し、次に有限回の確率実行、最後に無限学習の fairness/almost-sure 層を接続します。Lemma 3 の induction、query の安定化、Theorem 2 の極限と誤差を証明します。continuous PBS 全体の列挙や、一般 NN が exact memorizer になるとの仮定を隠しません。

**受入:** 再帰の停止、実際の sampling process の定義、必要な訪問性の証明、N/T/depth と value target の意味の明確化、Theorem 2 の本文/再掲差分の記録。

### M08 — CFR-AVG、FLOP、warm start を含む全変種

**依存: M04。各 PBS 変種は M06。** CFR-AVG の exact-subgame 版と Theorem 5、modified CFR-AVG の差分更新、FLOP と GWFP 条件/Theorem 4、Appendix J の warm start、linear/discounted の更新と加重平均を実装します。

modified CFR-AVG は一般保証を積極的に調べます。成立を証明できる領域、原文の条件付き主張、一般形の証明/反例を分け、未解決は未解決のまま表示します。FLOP の係数・初期 index・近似 best-response 定数も独立に確認します。

**受入:** 変種ごとの定義・証明の対象域・実験設定との対応、warm start の不正パラメータ排除、既存 vanilla 証明の誤流用を防ぐテスト。最終版では本段階を任意扱いにしません。

### M09 — 具体的学習/ネットワーク/数値実装

**依存: M07。仕様調査と一部実装は M03 以降並行可能。** 公式 `cfvpy/models.py`、`cfvpy/selfplay.py`、C++ solver/data-loop/replay、設定を関数単位で対応付けます。forward pass、activation、normalization、損失、勾配、optimizer、buffer eviction/sampling、target 作成、checkpoint、並列生成の snapshot/staleness を形式化します。

実数仕様 → 有理数基準 → 浮動小数点/quantization という refinement を進め、丸め、overflow、NaN、正規化の最小分母、tensor shape、乱数を扱います。GPU batching/TorchScript/FFI を含む外部境界は明示的な契約にします。検証可能な Lean 実行器は仕様への同値性を証明し、元 C++/Python の全プログラム同値性を示していない場合はそのまま区別します。

NN の学習更新を正しく実装したことと、任意の学習過程が value-error bound を満たすことは別命題です。収束定理が要求する oracle 契約を具体モデルが満たす証拠（定理または限定した領域の証明付き検査器）を追跡します。未証明の契約は最終の無条件保証に残せません。

**受入:** tensor/学習/データ生成の具体仕様と refinement、異常入力の処理、再現可能な test vector、数値誤差を M06 の bound に渡す bridge、外部 runtime と学習保証の未証明境界一覧。

### M10 — 全ゲーム規則と実験の再現性

**依存: M02 から規則実装を開始。統合は M08 + M09。** Liar's Dice、TEH、HUNL、action abstraction/off-tree insertion、stack/bet randomization を仕様化します。Liar's Dice は公式公開実装と照合します。TEH/HUNL は論文準拠であり、未公開コードの忠実な移植と名乗りません。

exploitability/NashConv/一人の best-response gain/saddle gap の係数と定義を固定します。近似 best response と exact best response を区別します。評価の sampling、policy averaging、分散低減、単位と誤差棒の意味、計測コードを監査します。学習済み重み・実験結果は provenance/hash と計算可能な検査対象を持たせます。

**受入:** 各ゲームの合法性/停止/零和/情報保護、評価計算の正しさ、原論文表・図の各設定と再現結果の台帳。実測値の一致を保証定理と混同しません。

### M11 — 完全性監査とリリース

**依存: M05 + M07 + M08 + M09 + M10。** 原典 inventory と公式実装 inventory の全行を再監査し、番号付き式・脚注・補助定理まで欠落を探します。全 source を build/lint/推移的公理検査に含め、可能な checker を固定 toolchain で再検証します。

原典どおりの証明、明示的前提付きの証明、修正版、反例、実験観測、外部 trust を別々に報告します。未解決行を削除して完成率を上げません。理論版の tag と実装版の tag に、それぞれ保証範囲を添付します。

**受入:** 再現可能な clean build、公理 allowlist、完全な原典/コード対応、意味的レビュー、未証明部分を隠さない成果説明。無条件正当性が閉じていないなら、その意味での「完全検証済み」とは呼びません。

## 依存関係と最初の数回

```text
M00 → M01 → M02 ─→ M03 ─→ M05 ───────────────────┐
                └→ M04 ─┬──────────────→ M08 ─────┤
                  M03 ──┴→ M06 → M07 → M09 → M10 ├→ M11
```

M10 の規則づくりは M02 から進めます。M08 の PBS 変種は M06 を消費します。Theorem 1 を証明するまで全 solver 作業を止める一本道にはしません。

最初の実装回は M01 の compiler loop と原典監査です。次に M02 の一つの非自明なゲームで情報/public-history の設計を検証し、その後 M03 の joint PBS を通します。一回のチャットで一段階すべてを終えることは要求しません。一回の成果は「同じ SHA で検証できた一つの補題群または縦断例」とします。

数日/数チャットで終わるという見積りはまだ置きません。M03/M04 の実測後に、残る証明義務と一回当たりの検証時間を用いて更新します。
