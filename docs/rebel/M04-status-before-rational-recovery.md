# ReBeL — 継続用状態

## 現在地

**M04 を `rebel/m04` で実装中。M04 と ReBeL 全体は未完了。**
main は受入済み M03 の `cf733bd1ffa977681d1197bf80b1dfd7be82ff6e`。
M03 の完了時 STATUS は `M03-status-history.md` に元の blob
`fd7bf887b6116c05f8a072585a1bd173e33c1fa3` のまま保存した。
M03 の verified=13 / qualified=11 と意味論境界は変更しない。

## 復旧済みのチェックポイント

- `7bcb033348cdc55d3b23db011a524ad14891ae77`: 前回保存済み有限 plan / 最良応答。
  build は通過したが、例の local instance の文書不足で lint が失敗していた。
- `db0d292361b2afcb136e2b6ed7f4aaaecbf15759`: 文書不足を修復。監査は緩和していない。
- `9859ae06e9ea99808690167fc47159f857c3de31`: 固定コンパイラの補助 module data を補完。
  ReBeL run `35295577895` / job `105447322333` は成功。
  artifact `10527563286` の実ログで35 modules の build・全 normal/slow lint と
  1367宣言の推移的公理監査を確認した。許容公理は従来の3種のみ。
  full CI run `35295577873` は別途最終結果を確認すること。

## 今回保存する証明スライス

`Schedule.lean` は全合法履歴から重複のない時系列スケジュールを構成し、
同深度の別情報集合・零到達確率の分岐も保持する。
`Analysis/ReBeL/LocalRegret.lean` は任意の残り手数と終端を含む情報集合で
局所 regret matching の実現等式を証明する。全体の後悔分解を仮定してはいない。
二段階 hidden-type ゲームの回帰例、解析側 public root、全 proof consumer への登録を含む。

固定 Lean 4.33.1 による手元コンパイル、追加54宣言への全通常・低速lint、
1405宣言の推移的公理監査、37 Python tests は通過した。
これはこの新しいコミット自身の Actions 成功の代わりではない。
次の再開時は実際の branch SHA / Actions 結果を確認する。
詳細な前提と未完了部分は `M04-schedule-local.md` を参照。

coverage の M04 項目はこの部分実装だけで完了に昇格しない。
旧台帳の3052項目・原典ID・既存証拠を保持する。

## 残りの実装順序

1. 実際の時系列方策置換から root regret 分解を導く。
2. 全情報集合の regret matcher を同一 profile 列に結合し、上界と有限反復 regret を証明する。
3. 自己到達確率による平均方策、零分母 fallback、独立な私的反復乱数との実現同値、
   二人零和ゲームの全合法逸脱に対する近似 Nash を接続する。
4. 明示的有理数 solver と実数仕様との refinement、T=0/1・零正regret・二段階の独立検査。
5. 対象SHAの全CI・lint・公理・意味論監査を確認し、coverage / STATUS を更新する。

主要段階を GitHub プラグインでコミット・反映する。main の未検証変更、force push、
worktree、依存pinの変更、監査基準の緩和はしない。受入時に一時的 compiler export workflow を除去する。
