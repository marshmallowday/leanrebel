# ReBeL — 継続用状態

## 現在地

**M04 は `rebel/m04` で継続中。ReBeL 全体も未完了。**
2026-09-19 の再開で GitHub プラグインから次のリモート ref を実読した。

- `rebel/m04`: `f646c009e0176f703da0e434296294c17e4d8440`
- `main`: `cf733bd1ffa977681d1197bf80b1dfd7be82ff6e`

前回の最終実装コミットはブランチに反映済み。既存の証明をやり直さない。
最新実装チェックポイントは `M04-concrete-final-checkpoint.md`。
その文書の「検証待ち」は作成時点の記録であり、以下の実読結果で更新する。
過去の STATUS は `M04-status-before-rational-recovery.md` に保存済み。
M03 の証拠・qualified 境界・原典の親義務と子台帳は保持する。

## 対象 SHA の実際の検証結果

対象は `f646c009e0176f703da0e434296294c17e4d8440`。

1. **ReBeL checks は成功。** run `35363536383`、job `105660357662`。
   静的構造監査、台帳/inventory、46 Python tests、実 Lean 有理数 solver の
   T=0/1/2 独立全探索照合、全 ReBeL build、通常/低速 lint、推移的公理監査、
   tracked-file cleanliness が成功。validation artifact は `10556275430`。
   正しい source artifact は `10554754280`（前回報告の番号は誤り）。
2. **全体 CI は失敗。** 正しい run は `35363536384`、job `105660678715`。
   前回報告の `35363536494` は誤記で、404 は権限障害ではない。
   全体 `lake build` は4089 jobs成功。inventory と Phase 1/2 は成功。
   Phase 3 が `LIBRARY_LINES_OVER_100: expected 0, got 7` で停止した。
   最大行長136。全体 lint と tracked-file cleanliness は未実行。
   したがって「全体 CI が進行中/確認不能」との前回報告は訂正する。

具体 runtime の履歴・情報集合・合法手・chance・payoff・continuation・reach・
反事実価値・局所 commitment・regret・全反復・own-reach average・canonical
approximate Nash への接続は ReBeL 対象でコンパイル/公理/lint 検証済み。
`solve_isNash` の存在を ReBeL 全体の完成や公式 C++ 同値性と取り違えない。

## 今回の復旧段階

既存の100文字制限を変更せず、ReBeL workflowのコンパイル前に違反箇所を
ファイル/行番号付きで報告する fail-fast 検査を追加する。
.NET文字列長に合わせてUTF-16 code unitsを数える。元のPhase 3監査も保持する。
この復旧コミット自体は新しいSHAであり、新SHAのCI結果は別途確認する。

## 次の作業

1. fail-fast出力の7行を改行のみで修復し、pluginでcommit/ref更新する。
2. 新SHAのReBeL checksと全体CIを実読し、残る実エラーを直す。
3. ROADMAPのM04受入条件と一般定理・具体例・独立検算・原典義務を照合する。
4. 検証と意味レビューに応じてcoverage/STATUS/受入記録を同時更新し、
   そのSHAの検証を確認してからmainを非forceで統合する。

GitHubの読み書き/操作はplugin、コンパイルはActions。
force push、未検証main更新、依存pin変更、監査緩和はしない。
最初の依頼全文は今回のコンテキストにもなく、履歴検索の要約を全文と偽らない。
今回は最新の継続指示、AGENTS、ROADMAPと保存済み成果から再開する。
