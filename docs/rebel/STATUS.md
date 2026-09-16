# ReBeL — 継続用状態

## 現在地

- 段階: **M00（準備）**。理論・アルゴリズムの ReBeL 新規 Lean 宣言は 0。
- 書込み先: `marshmallowday/leanrebel` のみ。
- 準備前 `main`: `5532a9c1d900261ae8e6ac4fe877ebd1c175cc1c`。
- 公式実装固定点: `7960a42750f3407ea9eb2c3333d4c2a7961f6df4`。
- 既存 Lean/Lake/依存/workflow は変更しない bootstrap。
- `coverage.json` の候補対応は未検証。既存部品の存在と ReBeL の主張への適用を区別する。

このファイルを書いた commit 自体の SHA を本文へ自己参照で埋め込まない。Git history から取得すること。後続の検証は、その検証対象 commit の SHA を下の欄に記録する。

## 検証と未確認事項

台帳検査器は JSON の整合性だけを調べる。Lean のパーサー/コンパイラー/カーネルの代用ではない。

準備時の環境確認:

- Git remote (`origin`) で leanrebel の読み取りと push 権限を確認。
- `lean-toolchain` は `leanprover/lean4:v4.33.1`。
- `lakefile.lean` は GameTheory 以下の全サブモジュールを default build に含め、warningAsError を指定。
- 既存 `.github/workflows/ci.yml` は push、pull_request、workflow_dispatch に対応。
- 準備時点の fork の Actions runs の初回照会は **0 件**。有効化済み/無効化中の設定そのものは未確認。
- 通常のサンドボックスからの GitHub 接続は失敗したが、昇格した Git remote 操作で読み書きを確認。ローカル Lean build は実行していない。
- 出版版本文・補遺のテキストを参照。補遺 G の Theorem 3 再掲の画像を確認。PDF 全ページの画像確認とバイトハッシュ取得は未完了。

準備ファイルのローカル検査:

- `python scripts/rebel/check_coverage.py`: 60 件すべて `pending` として構造検査に合格。
- 不正 repository、ID 重複、不正 status、証拠なし verified、未知 parent、循環 parent、パス逸脱、証拠なし refuted の 8 種の負例を拒否することを確認。
- 既存 `AGENTS.md` は Git blob `dec86866354917eda88f555419dfbd3c57793e3c` と一致する原文を保持し、fork 固有の入口だけを挿入。
- これらは文書・台帳検査器の検査であり、Lean 証明の検証結果ではない。

Lean 検証記録:

| 対象 commit | command / workflow | 結果 | 証拠 |
|---|---|---|---|
| baseline `5532a9c...` | `lake build` / 既存 CI | 未実行・未確認 | 次回取得 |
| ReBeL | narrow build / axiom audit | 該当コード未作成 | M01 以降 |

## 次に行う一作業: M01-A

**目的:** GitHub 経由で実際に Lean を検証できることを確認する。

1. 最新 main、ブランチ、対象 SHA の Actions runs を読み、他の作業を上書きしない。
2. fork の Actions タブで有効化が必要なら、その操作だけをユーザーへ案内する。公開 fork で自動実行されると推測しない。利用する GitHub 連携に workflow 有効化/任意 shell 実行の専用操作がない場合は、ユーザー操作が必要な箇所を明示する。
3. 既存 CI の manual 実行、または fork 内の小さい作業ブランチへの実質的な commit を用い、baseline と compiler-loop を確認する。自動実行の前提が成立していないなら先に解消する。
4. 最初の小さな Lean 成果として ROADMAP R3 の有理数診断不等式を証明し、余力があれば実数版を接続する。配置候補は `GameTheory/ReBeL/Tests/SourceDiagnostics.lean`。これは Theorem 1 の完成ではない。
5. 実在する対象の narrow build と推移的公理依存を検査する。許容されない依存がある場合は除去する。新しい lint/axiom-audit 組込み方法を確定する。
6. 成功 SHA と run/job ID、ログ、coverage、次の一作業を同じ変更系列へ記録する。未完了 CI は成功と報告しない。

その次は M01-B（原典の全項目化と R3/R5 の解釈監査）、M02-A（二段階隠れ情報ゲームの縦断例）。M01 の実行ゲートが閉じない間に、未コンパイルの PBS/CFR 実装を大量に作らない。

## 決定済み

- 原典監査と code coverage を論文 Theorem 1–3 だけに縮小しない。
- PBS は相関を保持する参照意味論から始め、コンパクト表現は同値性を証明してから利用。
- 個人 posterior と PBS、counterfactual value と normalized value、各平均/乱数の意味を分離。
- Theorem 1 は solver/safety 全体の唯一の進行ゲートにしない。
- NN、optimizer、replay、数値誤差、全変種、ゲーム規則は最終対象として維持。
- 原文が偽または曖昧な場合は原文・修正版・反例を分離。未解決のものは消さない。
- PDF の大量転載、空 `.lean` 群、`sorry` skeleton、新しい依存一式は追加しない。

## 次回チャット用プロンプト

```text
Git remote と利用可能な GitHub 読み取り手段で marshmallowday/leanrebel の最新状態を読み、
AGENTS.md、GameTheory/ReBeL/AGENTS.md、docs/rebel/README.md、
docs/rebel/STATUS.md、docs/rebel/ROADMAP.md、docs/rebel/coverage.json
を確認してください。STATUSの次の一作業からReBeLの完全Lean形式化を進めてください。

変更・commit・push・PRは marshmallowday/leanrebel 内だけ許可します。
原典の定義と前提を照合し、小さい検証可能な単位で実装してください。
実際の対象SHAでコンパイル/公理依存を確認できたものだけを検証済みとし、
検証不能なら理由と再開手順を残してください。原文の誤記・反例・条件追加は隠さず、
NN/学習/実装変種を最終範囲から削除しないでください。
最後にcoverageとSTATUSを更新し、commit、検証結果、残る問題、次の一作業を報告してください。
```
