# ReBeL — 継続用状態

## 現在地

**M03 の有限・参照意味論の受入条件を充足。次の実装段階は M04。ReBeL 全体は未完了。**
検証済みの実装 SHA は `703796b7a7a90b60851a0876ba99976b0be59341`。
作業ブランチは `rebel/m03`。M03 開始時の main は
`db95ea6ad79a26ff753093294722c779e109118d` だった。
この完了記録 commit の SHA と main への反映状況は、実際の GitHub refs/history で確認する。
このファイル自身の commit を、過去に検証した実装 SHA にすり替えない。

原典24項目を全て無条件に証明したという意味ではない。
M03 は **verified=13、qualified=11**。後者は対象域・追加条件・索引修正を明記した対応であり、
元の広い主張の証明に昇格させない。ROADMAP の「正確な対象域での strategic-equivalence」
を満たす有限モデルの受入と、原典の全解釈の完全な証明とは区別する。
詳細な原典対応と全宣言名は `M03.md`、実行証拠は `M03-compiler-log.txt` を参照。

## M03 の検証済み実装

次の3 job は全て 703796b を実際にチェックアウトし、最後の tracked-file cleanliness まで成功。
前回の会話に残った「全体lintが実行中」という記載は古く、実際には成功していた。

| 検査 | run / job | 確認した結果 |
|---|---|---|
| full CI | `35276996593` / `105390107946` | 全体build、23候補のLean型、Phase 1/2/3（2/3はdeep）、全体lint、tracked diff: 全成功 |
| ReBeL checks | `35276996529` / `105389909678` | 明示的33 modules、1771 build jobs、1348宣言の推移的公理監査、全33 normal/slow lint、tracked diff: 全成功 |
| source inventory | `35276996583` / `105389909669` | 公式ソース・固定PDFの再現、台帳、既存27 Python tests、tracked diff: 全成功 |

全体lintのbuildは3812 jobs。1348は生成補助宣言を含む数で、独立した論文定理の数ではない。
許容公理は `propext` / `Classical.choice` / `Quot.sound` のみで、全依存集合はその部分集合。
Lean 4.33.1、compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`。
依存pin、監査基準値、禁止公理・lint条件は緩和していない。

## 今回の復旧・完了記録

最初の依頼と制約を再確認し、GitHubプラグインで先端と3系統の成功を再取得した。
主要段階を次のように保存している。

- `72fe6fc1541247ff8259991d0f7b592ca452d162`: 成功済み実装と残作業の復旧チェックポイント。
- `dc6bc30ac6f10cca27980d59614c93e57e0b7430`: 実行証拠の追跡可能な抜粋と、更新前台帳の不変fixture。
- この完了記録: M03原典対応、coverage、STATUS、受入用回帰テスト。SHAはGit履歴から取得する。

今回の変更は台帳・文書・Python回帰テスト/fixtureであり、703796b のLeanソース、
production validator、workflow、toolchainを変更しない。既存の全検査に加えて、
失敗済み旧SHAへの差替え、source blobの偽装、qualifiedの無断昇格、前提削除を拒否する
受入テストを追加した。これらの新しいテストの実行結果は、この完了記録commit自身の
Actionsで確認すること。703796bの既存27テスト成功を、新規テストの実行証拠とは呼ばない。

coverage全体は3052項目: **verified=40、qualified=11、context_indexed=405、pending=2596**。
項目数を完成率や独立定理数と解釈しない。原典のID・親・locator・主張・milestone、
M01/M02の既存証拠、paper.tsvとofficial.json.gzの固定ハッシュを保持している。
`coverage_pre_m03.json` は更新前のGit blob `0e5648d3ab155fe4a0c998d2d3854c14d6593925`
そのものであり、既存証拠の保存を回帰検査する基準である。

M01/M02時点のSTATUS全文は `M02-status-history.md` に同じblobのまま保存した。
そこにある「次はM03」「PBS-POLICY-DOMAINは未完了」等は過去の状態であり、現在地ではない。

## 保持する意味論境界

公開履歴に対応する joint history law からPBSを構成し、正の確率でのみBayes条件付けする。
零確率観測は `none`。非正規化reach weightと確率分布は別型。
chance/compatibilityを残したcompact表現と実際の公開条件付き履歴分布との一致を証明した。
同じゲームの同じ公開fiber上で周辺分布が等しくても、継続期待報酬が2と0に分かれる。
この2つの支持条件付きPBSを、同じ固定priorから到達する事後分布だと主張してはいない。

方策制限・拡張は特定profileの支持だけでなく、全ての合法履歴を対象にする。
終端・構文上不可能なAOHへの拡張には、明示的な合法fallbackを要求する。
両方向のoutcome・期待報酬・単独逸脱・Nash対応は、元の公開履歴を添字とする
情報局所prescriptionについて成立する。相手の完全なplanの追加公表に自由に反応する
拡張ゲームの全戦略まで同値だとする主張は未証明のまま明記する。

104/156や2*F^D等は可変な局所vectorの要素数であり、固定chanceデータ・公開keyを含む
普遍的な総メモリ/実行時間の上限ではない。一般の周辺分布積、任意のstate圧縮、
完全なpoker/C++ encoderの正当性は今回の結果から導かない。
完全情報での退化には公開traceによる履歴の識別を要求し、全AlphaZeroとの同一性は述べない。
qualifiedの11原典項目はM11の完全性監査にも引き継ぐ。元の広い義務を削除しない。

## 中断時の再開手順

GitHubプラグインで main と rebel/m03 の先端、最新commit、対象SHAのActionsを取得する。
この完了記録の変更が保存され、3系統の検査が成功していれば、実装済みの703796bを作り直さない。
mainがまだ旧先端なら、別の更新がないことと祖先関係を再確認し、force=falseのfast-forwardで統合する。
mainとrebel/m03が同じ受入済みcommitを指していれば、M03の受入・保存・統合は終了している。
失敗した場合は該当する実ログと変更差分だけを修正し、主要段階でcommitとリモート反映を確認する。
GitHubアクセスはプラグイン経由、Lean実行はActionsで行う。worktree/reset/force-pushは使わない。

## 次段階 M04 と未完了の全体義務

M04では任意の対象有限ゲームに対する全情報集合のCFR scheduler、反事実値の実現、
root regret分解、own-reach加重平均、全逸脱に一様なfinite-T bound、実行可能solverと
独立brute-force検算を進める。`BR-ATTAINMENT` は依然pendingで、IsGreatestの特徴付けを
最良応答の存在や計算アルゴリズムに読み替えない。
M05以降のvalue幾何、Theorem 1、探索誤差、学習・各変種、NN/optimizer/replay、
数値実行、全ゲーム・評価と公式実装refinementも未完了。oracle-onlyに縮小しない。
