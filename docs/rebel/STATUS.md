# ReBeL — 継続用状態

## 現在地

- **M01-A 完了。M01-B の原典棚卸し・R1–R7監査を実施済み。更新後SHAの統合検証中であり、M01全体の完了はまだ宣言しない。**
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

## M01-B の成果と現在の統合ゲート

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
  一時writer/workflowは本統合候補から削除し、通常CIはread-onlyを維持。
- **残る一作業:** この更新後ブランチSHAのfull build/lint/architecture、23候補のcompiler型確認、
  ReBeL公理監査、原典index/PDF比較、23 Pythonテストの実ログを取得して統合ゲートを閉じる。
  実行中を成功と扱わない。完了後coverage/STATUSを更新し、main先端再取得後にfast-forwardする。

既存Windows main run `35134440926` はPhase 3でcancelledであり成功扱いしない。
全検査成功を確認した対象はUbuntu。Windows manual経路は保持し、検査を削っていない。
Actions基盤のNode 20/24 deprecation warningとLeanの警告・エラーを混同しない。

## M01統合後の次タスク: M02-A

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
