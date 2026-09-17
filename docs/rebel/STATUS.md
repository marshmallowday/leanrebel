# ReBeL — 継続用状態

## 現在地

**M02 完了。次の作業は M03。ReBeL 全体の形式化はまだ完了していない。**
作業ブランチは `rebel/m02`。M02 開始時の main は
`8beff57b70f3c5e28fb28724c655207ced881c88`。
中断時の `d07b17315ab31788dec2c4a87b5d0c2ba47fe0c0` までのコミットは全て保存済みだった。
回復時に main より52コミット先行・0遅れと確認し、reset/force-push/worktreeは使用していない。
受入対象95dbfb2はその後継で、監査分類漏れと12行の文字数超過を修正した。
実際の最新 main と記録commitのSHAは GitHub の refs/history を取得して確認すること。
このファイルは、自己参照の完了記録commitを過去の検証対象SHAとして扱わない。
書込み先は `marshmallowday/leanrebel` のみ。通常CIはread-onlyであり、一時blob準備workflowは
完了記録commitから削除する。以下のM01記録は履歴として保持し、現在の状態と混同しない。

## M02 最終受入

**M02 完了。受入対象の実装 SHA は `95dbfb2a32175038938315a3da5026deb4287610`。**
論文全体・ReBeL 全体の形式化完了ではなく、ROADMAP の M02 に限る。
次段階は M03。検証対象 SHA と、その後の完了記録 commit は区別する。

| 検査 | run / job | 実ログで確認した結果 |
|---|---|---|
| full CI | `35243144402` / `105276473279` | 全体 build 4027 jobs、23候補型、Phase 1/2/3（2/3は deep）、public lint 3797 build jobs、tracked diff: 全成功 |
| ReBeL checks | `35243144308` / `105276776415` | 明示的17 modules、1752 build jobs、963宣言の推移的公理監査、全17 module lint、23 Python tests、tracked diff: 全成功 |
| source inventory | `35243144305` / `105276430059` | 公式53エントリ・2578出現、PDF50頁・25版対応の再現、台帳・23 Python tests・tracked diff: 全成功 |

full CI の最後の public lint は 2026-09-17T16:09:33Z に成功した。
ReBeL の最終マーカーは `REBEL_VALIDATION_PASS modules=17`、公理監査は
`REBEL_AXIOM_AUDIT_PASS declarations=963`。963は生成補助宣言を含み、963個の独立定理ではない。
許容公理は propext / Classical.choice / Quot.sound のみ（各宣言はその部分集合を使用）。
Lean 4.33.1、compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`。
この検証で sorry/admit・独自公理は0。依存 pin と既存の監査基準値は変更していない。
ReBeL 層は新しい明示的測定区分として58個の `change` を登録し、非定義的 transport は0。
未分類ファイル0、100文字超過行0、Phase 2/3 の deep probes も含めて合格した。
修正過程と負例検査は `M02-integration.md` を参照。

### coverage と完了記録の検査

M02 は27項目（`verified=26`, `context_indexed=1`）。脚注3の「方策が既知」は
モデル前提の説明として分類し、観測していない乱数や隠れ状態を知る定理にはしていない。
全体は3052項目（`verified=27`, `context_indexed=405`, `pending=2620`）。
元の3048項目の ID・親・原典・locator・主張・milestone を全て保持した。
M01-B の原典索引ハッシュと、DIAG-R3-Q の既存証拠も変更していない。
項目数を形式化完成率や証明数として解釈しない。

元の23 Pythonテストは、厳密に同じ M01-B coverage blob を不変fixtureとして保持して再実行した。
さらに現在の台帳と原典3048項目の同一性・既存検証証拠の保存を検査する1テストを追加し、
合計24テストに合格した。完了記録の変更は台帳・文書・Pythonテスト/fixtureだけであり、
95dbfb2 の Lean ソースや production validator / workflow / toolchain は変更しない。
完了記録用の実行証拠: run `35245853980` の `METADATA_REGRESSION_PASS tests=24`。

## 追加の意味論境界と未完了義務

`Response.isBestResponse_iff_policyValue_greatest` は、任意の固定された合法な相手方策に
対する最良応答の最大値による特徴付けである。相手に Nash 性を仮定しないが、最大値を
達成する方策の存在や計算アルゴリズムを証明したことにもならない。
その存在義務を `BR-ATTAINMENT`（M04、親 FOUND-NASH）として明示した。

一般の InformationModel の menu_adequate は実現した履歴上の合法性を保証するもので、
到達不能な構文上の全 AOH に非空な menu を自動で保証するものではない。
一般の実行保存定理は供給された合法方策について述べ、縦断例では
fullPlanPolicy / fullBidCallPolicy を実際に構成して非空性を示している。
これを「全ての抽象モデルで方策空間が非空」「実現情報集合への制限と拡張が一般に同値」と
読み替えない。終端・構文上不可能な観測の扱い、実現可能だが特定方策で確率0となる履歴の
合法な逸脱を保持した方策領域の同値性は `PBS-POLICY-DOMAIN`（M03）に残す。
この項目は PBS-EQUIVALENCE の分解であって、元の義務の削除・弱化ではない。

M02-HIDDEN-TYPES と M02-LIARS-INSTANCE は今回の限定された非自明な縦断例の証拠であり、
GAME-LIARS の一般パラメータ/C++ refinement 義務は pending のままである。
P-DEP-02/P-DEP-34 は実際に必要な有限鎖の共通知識解釈と FOSG 観測・完全記憶の前提を
直接証明・具体化した範囲に限る。引用文献全体の再形式化を宣言していない。
M03 の joint PBS/conditioning/戦略同値性、M04 のCFRと均衡存在、後続の学習・数値実行・
一般ゲームと公式実装 refinement は引き続き未完了である。

## M01 受入記録の保存

## M01 時点の現在地（履歴）

- **M01（M01-A → M01-B）完了。次の作業は M02-A。ReBeL 全体の形式化はまだ完了していない。**
- M01-A の完了ログを確認する前に M01-B の原典棚卸しには着手していない。
- 書込み先: `marshmallowday/leanrebel` のみ。作業ブランチ: `rebel/m01-b`。M01-A先端 `ec152983ce74c6d5c56bf5e16ae6add5e1bab245` を保持。
- 作業開始時 main: `c66c51c8917748bc1f64e3d0548dbe54921dba4e`。
- 準備前 baseline: `5532a9c1d900261ae8e6ac4fe877ebd1c175cc1c`。
- 公式実装固定点: `7960a42750f3407ea9eb2c3333d4c2a7961f6df4`。
- 新規 Lean 成果は R3 の有理数診断: 2 定義、12 定理。ゲーム意味論・PBS・CFR の実装ではない。
- 論文 Theorem 1 本体は未証明・未反証。親台帳の主張を縮小していない。

このファイルを書いた commit の SHA は自己参照で埋め込まない。Git history から取得すること。
下の SHA は、実際に実行ログを確認した検証対象である。

## 検証済みの実行記録

| 対象 | 実際の checkout SHA | run / job | 結果 |
|---|---|---|---|
| historical baseline | `5532a9c1d900261ae8e6ac4fe877ebd1c175cc1c` | `35139613333` / `104940546791` | full build、public lint、Phase 1/2/3（deep 含む）、tracked diff 検査: 全成功 |
| ReBeL 診断 | `585326121c3ebd64ac78fba1e09cab1e6bcfb461` | `35141101465` / `104945539666` | narrow build、公理監査、明示的 test-module lint、coverage 構造、tracked diff 検査: 全成功 |

フルログを取得して確認済み。診断の公理監査は補助宣言込み **16 宣言**を検査し、
すべて `[propext, Classical.choice, Quot.sound]` のみだった。
Lean 4.33.1 / compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`。
依存 pin・Lake オプション・既存 architecture expected count は変更していない。

詳細、正例・負例・境界例、宣言の意味と限界、再現コマンドは `M01-A.md`。
3 回の実際の失敗と修正は `M01-A-failures.md` に記録した。
通常のローカル環境では Lean は実行しておらず、上記は GitHub Actions による実行である。
台帳検査器は証明検査ではない。ローカルでは有効データと 8 種の不正台帳 fixture を確認した。

## M01-B の成果と受入証拠

- `M01-B.md` に本文・補遺・arXiv v2・公式実装、R1–R7、引用依存、再利用前提を記録。
- `inventory/` は論文356項目、公式53エントリ（51ファイル・2 gitlink）と2578構文/設定出現を追跡する。
- `coverage.json` の親61項目とハッシュ付き子台帳を合わせて3048項目。
  `pending=2643`, `verified=1`, `context_indexed=404`。項目数は証明完成率ではない。
- 23候補宣言・17モジュールの型/前提を記録。存在の確認と適用可能性の証明は別。
- ローカルの構造/改変検査20件と独立誤差漸化式の有理数検査3件は成功。
  漸化式テストはゲームの有限反復誤差定理の証明ではない。
- M01-B前の最新SHA `ec152983ce74c6d5c56bf5e16ae6add5e1bab245` について、
  full CI `35142659993` / `104951188305` と ReBeL `35142660014` / `104950755521` は全成功。
  full build 4011 jobs、public lint、Phase 1/2/3 deep、16宣言の推移的公理監査を実ログで確認。
- 生成データの完全再現は `63262218154269395214db788f5b58cac5743884` の
  run `35149443912` / job `104973717567` で成功。生成4blobのSHA256がレビュー済み値と一致。
  この一時jobは当該リポジトリ内のblobだけを保存し、ref/commitを変更していない。
  一時writer/workflowは受入対象9ecbc4641907から削除し、通常CIはread-onlyを維持。

**M01-B の実装・監査成果の受入対象は `9ecbc4641907c8ddbc8181836036dab4de797759`。**
以下の3 workflowはすべて完了・成功で、各jobのフルログを取得して確認した。

| 検査 | run / job | 実ログの結果 |
|---|---|---|
| full CI | `35151402989` / `104980487227` | full build 4011 jobs、23候補の実際のLean型、Phase 1/2/3 expected count、Phase 2/3各8件のdeep probe、全public lint 3781 jobs、tracked diff: 全成功 |
| ReBeL checks | `35151402962` / `104980333101` | coverage/inventory、23 Pythonテスト、narrow build 816 jobs、16宣言の推移的公理監査、明示的test-module lint、tracked diff: 全成功 |
| source inventory | `35151403168` / `104980332983` | 公式53エントリ・2578出現の完全再生成、PDF50頁・25版対応のハッシュ比較、coverage/inventory、23 Pythonテスト、tracked diff: 全成功 |

公理監査では全16宣言が `[propext, Classical.choice, Quot.sound]` のみに依存することを再確認した。
再利用候補の型は `REUSE_COMPILER_TYPES_PASS declarations=23` で確認したが、
全候補を `candidate_not_applied` のままにした。これはReBeLでの適用可能性の証明ではない。
M01-A先端から受入対象9ecまでにLeanソース・toolchain・依存pinの変更はない。

coverage の `inventory_status` は `M01_B_complete` とした。
この完了記録commitはSTATUSと当該ラベルのみを変更する。
上の実行証拠を自己参照の完了記録commitにすり替えず、対象SHAを明示して保持する。
完了記録commit自身のCI状態と実際のmain先端はGitHubから確認すること。
mainへの統合は先端を再取得したうえで通常のfast-forwardを用い、force-pushしない。

展開台帳でM01に属する73行は `context_indexed=72` と `verified=1`。
残る `pending=2643` はM02–M11の形式化義務であり、原典索引の完了を数学的証明の完了に読み替えない。
R3/R5の初期診断と原典解釈の監査はM01で完了したが、元ゲームへの埋め込みや
solverの誤差伝播を証明する後続義務は削除していない。

既存Windows main run `35134440926` はPhase 3でcancelledであり成功扱いしない。
全検査成功を確認した対象はUbuntu。Windows manual経路は保持し、検査を削っていない。
Actions基盤のNode 20/24 deprecation warningとLeanの警告・エラーを混同しない。

## M01 時点の次タスク: M02-A（現在は完了）

二段階隠れ情報ゲームの縦断例を作る。PBSは相関を保持し、ゼロ到達・off-pathと
情報漏洩の負例を含める。未コンパイルのPBS/CFR実装を大量追加しない。
R3の診断をVAL-THEOREM1の全解釈の反証に昇格させない。
R5では原文の誤差項と独立漸化式の候補を分離し、solverが漸化式を満たす証明をM06に残す。

## 決定済み

- 対象は原典本文・補遺・全変種・NN/optimizer/replay・数値実行・全ゲーム/評価。oracle-only に縮小しない。
- PBS は相関を保持する参照意味論から始め、compact encoding は同値性を証明してから利用する。
- 個人 posterior/PBS、counterfactual/normalized value、各平均/乱数を分離する。
- 原文が曖昧または偽なら原文・条件追加・修正版・反例を分け、未解決義務を消さない。
- 空 Lean module、証明 placeholder、新公理、監査値の引上げ、無関係な依存更新は禁止。
- 次回はこの STATUS と coverage、実際の GitHub 先端/CI から再開する。背景監視は約束していない。
