# ReBeL — 継続用状態

## 現在地

**M04 は `rebel/m04` で継続中。M04 と ReBeL 全体は未完了。**
2026-09-18 の再開時に、リモート HEAD
`22c6c999d8ea511abe6205353429d39e7d2ba73f` を GitHub プラグインで確認した。
最後の commit と branch ref 更新は成功しており、未反映の最終コミットはない。
main は実読で `cf733bd1ffa977681d1197bf80b1dfd7be82ff6e` のまま。
旧 STATUS は `M04-status-before-rational-recovery.md` に元の blob のまま保存した。
M03 の証拠・qualified 境界・原典台帳は保持する。

## 最初の依頼と読取の限界

今回のコンテキストには最初の M04 依頼全文がない。履歴検索を二通り試したが、
得られたのは要約であり全文ではない。`M04-document-review.md` の過去の全文読了記録を
今回の原文再確認と同一視しない。確認できた制約は、docs/rebel 全読了、M04 完了、
既存不備の修正、主要段階ごとの plugin commit/push、許可待ちで不要に停止しないこと、
worktree 回避である。最新のユーザー指示と AGENTS/ROADMAP を併せて継続する。
GitHub 読み書きは plugin、コンパイルは Actions を使う。

## 検証済みの進展と未検証の区別

`fbe3c805d2dcffd7c528edb0d5c3f59fc82c3ff1` の ReBeL run
`35347213313` / job `105606504621` では、一般の real CFR、root regret、
private own-reach averaging、canonical approximate Nash と具体例がコンパイル済み。
有理数の arithmetic/evaluation/reach/counterfactual/iteration refinement もコンパイル済み。
同 run の46 Python tests と T=0/1/2 の実 Lean solver 独立全探索照合は成功した。
ただし `RationalAverage.lean` の zero cast で失敗し、後続 lint/axiom audit は未完了。
zero cast は `22c6c99` で修正されたが、その新 SHA の ReBeL run `35348183808` /
job `105609659342` はコンパイル前の静的監査で停止した。
原因は `Examples/RationalCodec.lean` の3個の `change` による
`TRANSPORT_ANALYSIS_SOURCE: expected 0, got 3`。権限不足・push失敗ではない。

今回の復旧コミットは既存の証明目標・監査基準を変えず、3箇所で canonical support
の型付き補題を直接使用する。新しい SHA の CI を確認するまで成功と扱わない。
一般の rational averaged-output theorem と concrete history codec の受入はまだ保留。

## 次の作業

1. この復旧コミットの ReBeL checks と full CI の結果を確認し、実エラーを修復する。
2. Runtime Row/Site の情報・合法手・遷移・reach の対応を証明し、具体的な有理数
   solver と一般の canonical solver theorem を接続する。履歴全単射だけでは不十分。
3. 正確な対象 SHA で全 build、normal/slow lint、構造監査、推移的公理監査を確認する。
4. 原典・具体例との意味レビュー後にのみ coverage を昇格し、STATUS を更新して統合する。

force push、未検証 main 更新、依存 pin 変更、監査緩和はしない。
詳細な独立検算は `M04-rational-runtime.md`、過去の全文読了範囲は
`M04-document-review.md` に保存されている。
