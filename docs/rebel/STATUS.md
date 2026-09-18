# ReBeL — 継続用状態

## 現在地

**M04 は `rebel/m04` で受入検証中。ReBeL 全体は未完了。**
2026-09-19 の再開で plugin からリモートを確認した。
再開元は `f646c009e0176f703da0e434296294c17e4d8440`、
main は `cf733bd1ffa977681d1197bf80b1dfd7be82ff6e` のまま。
前回の最終実装はブランチに反映済み。完成した証明を再実装しない。

## 検証済みの基準

`f646c009e0176f703da0e434296294c17e4d8440` の ReBeL checks は成功。
run `35363536383` / job `105660357662`。46 Python tests、実 Lean solver
T=0/1/2独立全探索照合、全ReBeL build、通常/低速lint、推移的公理監査、
tracked-file cleanlinessを確認した。validation artifact `10556275430`、
正しいsource artifactは `10554754280`。

全体CIの正しいrunは `35363536384` / job `105660678715`。
4089-job buildとinventory/Phase 1/2は成功したが、Phase 3の
`LIBRARY_LINES_OVER_100: expected 0, got 7` で失敗。最大幅136。
全体lintとcleanlinessは未実行。前回報告のrun `35363536494` は誤記であり、
その404をアクセス障害と解釈しない。「進行中/確認不能」との報告も訂正する。

## 保存済みの復旧

`609d111a4b247a04bd75f2598c5baeadbdb91133` は再開状態と早期幅検査を保存。
run `35371274354` / job `105685560599` は同じ7違反を特定した。
`a5502224e6a337b6dbfca033c6a42aef06c8df1e` は5宣言行と2CSV出力行を改行。
直後の差分レビューで、その全ファイル置換時に混入した余分な引数2箇所を発見。
本コミットで両方を元の検証済み呼出しへ戻す。現在の新SHAはCI検証待ち。
`M04-width-recovery.md`、`M04-concrete-final-checkpoint.md`も参照。

実装の正味変更は宣言の空白とCSV文字列の同一内容の連結のみ。
定理の前提/結論、solver、テスト、依存pin、監査基準は維持する。
新SHAのReBeL checksと全体CIが成功するまではM04受入やmain統合を行わない。

## 次の作業

1. この最新refのReBeL checksと全体CIの実結果を取得し、残る実エラーを直す。
2. ROADMAP M04の一般solver、全deviation finite-T bound、private own-reach
   realization、二段階具体例、有理数refinement、独立検算を意味レビューする。
3. 証拠とcoverage/STATUSを同時更新し、そのSHAのCIを確認してmainへ非force統合。

GitHub読み書きはplugin、コンパイルはActions。M03の証拠・qualified境界・
原典親義務/子台帳を保持。M05以降のPBS value/existence、CFR-D、各変種、
学習、公式実装同値性はM04の完了と混同しない。
最初の依頼全文は現在のコンテキストになく、検索で得た要約を全文と偽らない。
