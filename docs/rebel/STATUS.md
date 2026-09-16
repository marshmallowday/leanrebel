# ReBeL — 継続用状態

## 現在地

- **M01-A 完了。M01-B が次の一作業。M01 全体は未完了。**
- M01-A の完了ログを確認する前に M01-B の原典棚卸しには着手していない。
- 書込み先: `marshmallowday/leanrebel` のみ。作業ブランチ: `rebel/m01-a`。
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

## M01 の残るゲート

1. M01-B: 原典 PDF のバイトハッシュ・全ページ画像確認、全定義・式・定理・擬似コード操作・公式関数/設定の子台帳化。
2. M01-B: R3/R5 の原文・版差・修正版候補の分離、引用依存と再利用候補の前提監査。
3. M01 統合: 更新後ブランチの full build/lint/architecture audit と coverage 検査。
   実行中ジョブを成功と記録しない。main 統合前にブランチ先端を再取得する。

既存 Windows main run `35134440926` は Phase 3 で cancelled のため成功扱いしない。
厳密な historical baseline は別 Ubuntu run で全成功した。
CI は同じ全チェックを Ubuntu で既定実行し、Windows は manual input で選択可能にした。
これは Windows 全検証の成功宣言ではない。検査項目は削っていない。

## 次の一作業: M01-B

`README.md` で固定した本文・補遺・arXiv v2・公式 commit を取得し、原典全項目を
台帳の子行として展開する。R3 の診断だけで VAL-THEOREM1 を refuted にしない。
Theorem 2 の N/T・値/方策・量化、Theorem 3 の誤差項、各 solver 変種を別項目に保つ。
既存候補の存在と適用可能性を混同しない。

M01-B と統合ゲートが閉じた後の次タスクは M02-A（二段階隠れ情報ゲームの縦断例）。
未コンパイルの PBS/CFR 実装を大量に追加しない。

## 決定済み

- 対象は原典本文・補遺・全変種・NN/optimizer/replay・数値実行・全ゲーム/評価。oracle-only に縮小しない。
- PBS は相関を保持する参照意味論から始め、compact encoding は同値性を証明してから利用する。
- 個人 posterior/PBS、counterfactual/normalized value、各平均/乱数を分離する。
- 原文が曖昧または偽なら原文・条件追加・修正版・反例を分け、未解決義務を消さない。
- 空 Lean module、証明 placeholder、新公理、監査値の引上げ、無関係な依存更新は禁止。
- 次回はこの STATUS と coverage、実際の GitHub 先端/CI から再開する。背景監視は約束していない。
