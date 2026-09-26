# ReBeL 完全形式化 — 入口

この fork の目的は Brown, Bakhtin, Lerer, Gong (2020) の ReBeL を、本文・補遺・アルゴリズム変種・学習/数値実装まで追跡して Lean で形式化することです。Theorem 1–3 や抽象 value oracle だけでは最終完了にしません。

**M05 の有限ゲームにおける PBS 均衡値・infostate 最適反応・Theorem 1 の採用解釈を検証済みです。補遺の径方向拡張や任意線形結合に関する誤った主張は、修正版と区別して反証を記録しました。[M05.md](M05.md)、[M05-validation.md](M05-validation.md)、[STATUS.md](STATUS.md) を参照してください。M04 の CFR と有理数 solver の成果は維持され、ReBeL 全体の形式化は M06-M11 が未完了です。**

## 読む順序

1. リポジトリ直下の `AGENTS.md` と `GameTheory/ReBeL/AGENTS.md`。
2. [STATUS.md](STATUS.md): 現在位置、検証結果、次の一作業。
3. [ROADMAP.md](ROADMAP.md): 範囲、依存関係、段階ごとの受入条件。
4. [coverage.json](coverage.json): 原典と成果の対応台帳。候補コードの存在は証明完了を意味しません。
5. [M01-A.md](M01-A.md)、[M01-B.md](M01-B.md): 実行記録、原典・版差・前提監査。`inventory/` はハッシュ固定の子台帳と出典です。

変更可能な GitHub リポジトリは **`marshmallowday/leanrebel` のみ**です。upstream、公式 ReBeL、他の fork への push・PR・issue 等は行いません。

## 原典と固定点

| ID | 対象 | 固定点・参照 |
|---|---|---|
| main | NeurIPS 2020 本文 | [出版版 PDF](https://papers.nips.cc/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Paper.pdf) — 13 PDF pages |
| supp | 同補遺 | [出版版 PDF](https://papers.nips.cc/paper_files/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Supplemental.pdf) — 12 PDF pages、印刷頁 14–25 |
| arxiv | 版の照合用 | [2007.13544v2](https://arxiv.org/abs/2007.13544v2)。出版版と同一と決めつけず、相違は記録する |
| base | leanrebel の開始点 | `5532a9c1d900261ae8e6ac4fe877ebd1c175cc1c` |
| official | Meta 公開実装 | [`facebookresearch/rebel@7960a42750f3407ea9eb2c3333d4c2a7961f6df4`](https://github.com/facebookresearch/rebel/tree/7960a42750f3407ea9eb2c3333d4c2a7961f6df4) |
| toolchain | Lean | `leanprover/lean4:v4.33.1`。Mathlib、補助依存は既存 `lake-manifest.json` を維持する |

PDF はここへ転載していません。M01-B で本文・補遺・arXiv v2 のバイトハッシュ、全50頁の比較用ハッシュ、全出版頁と異なるarXiv頁の画像確認を記録しました。取得 URL・SHA-256・版・ページ番号は `inventory/sources.json`、解釈の監査は `M01-B.md` を参照してください。

公式実装の README は公開対象を Liar's Dice に限定しています。HUNL/TEH は論文の規則・設定を基に再構成し、非公開の Meta ポーカー実装との同一性は主張しません。公式コードを移植・転載する場合は、その Apache ライセンスと著作権表示を保持します。論文 PDF の再配布許諾とは区別します。

追加の参照資料は、最初に必要な証明を担当する回で原典を取得して台帳に登録してください。優先候補は本文の CFR、CFR-D、FOSG、GWFP、warm-start の引用文献です。二次解説や過去のチャットを定理文の根拠にしません。

## 「完全」の意味

- **理論**: 定義・式・補題・定理・アルゴリズムと、使う外部定理の依存を追跡し、Lean の定理と原文の意味を照合する。
- **実装**: oracle 抽象化の後に、実際の solver、学習、ネットワーク、データ生成、数値表現を追加し、抽象仕様との対応を証明する。差分テストだけを実装同値性の証明と呼ばない。
- **原典監査**: 誤記・不明確な前提・反例があれば、原文、解釈、修正版、証明/反例を別々に残す。修正版の証明を原文そのままの証明と呼ばない。
- **実験**: ゲーム規則、評価関数、実験設定、統計計算を形式化し、再現実験の観測は別に記録する。「人間に勝った」という歴史的観測を Lean が演繹したと扱わない。

GPU、OS、PyTorch/C++ ランタイム等の全ソフトウェア・ハードウェア検証を暗黙に含めません。ただし、それらに依存する箇所の trusted boundary と未証明の refinement は必ず明記します。抽象 ReBeL と具体実装のどちらを保証したのかを最終成果物で分離します。

## チャット間の作業ループ

最新 `main` と前回の作業ブランチを読み、STATUS の次のタスクを一つ選びます。実装時は fork 内の `rebel/<task-id>` ブランチで、定義 → 小さい証明 → 意地悪な具体例 → コンパイル/公理監査 → 原典照合 → 台帳/STATUS 更新を一組にします。成功した対象 SHA のログを確認してから fork の `main` に統合します。基盤変更時だけ既存の設計記録・ExperimentLog も更新します。

GitHub の読み書きツールは Lean 実行器ではありません。利用できる実行環境を確認し、なければ fork の GitHub Actions を利用します。実行できない回は未検証と明記し、未コンパイルの大量実装を main に蓄積しません。長い CI が未完了なら run ID・対象 SHA・次に確認する点を STATUS に残します。

## M07以降のブランチ運用（2026-09-26のユーザー決定）

M07以降は各マイルストーンの統合先ブランチを1本に固定します。通常の続きや
小さな修正は同じブランチで進め、チャットの切り替えだけを理由に新しい
ブランチを作りません。大きな試案や並行作業は一時的な作業ブランチで行い、
採用する変更を検証して統合先へ戻します。重要な検証済み地点は対象コミットSHA、
必要に応じてタグで記録します。上記のチャット間ループのブランチ選択は、
M07以降この方針に従い、作業単位の成果はまず当該マイルストーンの統合先へ
集約します。M06の既存ブランチを一括削除する決定ではありません。

## 検証

台帳の構造だけを検査するコマンド:

```text
python scripts/rebel/check_coverage.py
python scripts/rebel/check_coverage.py --expanded-json
python scripts/rebel/check_inventory.py
python -W error -m unittest discover -s scripts/rebel/tests -v
```

Lean コードを追加した後に実行するコマンド:

```text
lake env lean --version
lake build GameTheory.ReBeL GameTheory.Analysis.ReBeL
python3 scripts/rebel/audit_axioms.py
python3 scripts/rebel/check_rational_runtime.py --report .lake/rebel/runtime.json
lake build
lake lint
```

`GameTheory.ReBeL` は基礎・実行側、`GameTheory.Analysis.ReBeL` は解析・証明側の実在する umbrella です。推移的公理監査と通常/低速 lint は双方を再帰的に検査します。

既存 CI は push/PR/manual 実行に対応し、全 GameTheory サブモジュールと既存の architecture audit をビルドします。fork 側の Actions 実行を M01-A で確認済みです。ReBeL 診断は対象モジュールを実際に列挙する lint/axiom audit に含まれます。新規モジュールでもこの消費側への接続を維持してください。台帳検査だけでは Lean の正しさは検証されません。

参考: [Lean の証明検証](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)、[GitHub fork の workflow](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows)。将来の API 変更より、固定 toolchain での実測を優先します。
