# Smale 5 的 Lean 形式化

本仓库保存基于五体中心构型手稿 v16 的 Lean 证明组件，以及相应蓝图、核验记录和形式化改写稿。

已核验：20 个模块、121 个公开辅助定理。包括真实规范化方程、质心与 U=I、固定距离和四乘积纤维有限性、规范化可微路径的能量常量性、Diagram 3 和 Diagram 7 的若干关键恒等式，以及相似类有限性到规范化配置有限性的衔接。

## 复现

安装 elan 管理的 Lean 和 Python 3.10 或更新版本，在仓库根目录运行：

```text
lake exe cache get
python scripts/check.py
```

`lean-toolchain` 固定 Lean 4.35.0；`lake-manifest.json` 固定 Mathlib 及其依赖。检查脚本不依赖 Archon 或外部模型服务，逐模块编译并审计全部公开定理。

## 当前主命题状态

`Smale5.FiveBodyFiniteness` 是最终目标命题。手稿本身的完整证明还需补齐代数曲线提取、曲线完备化及阶数理论、局部图分类和计算证书的连接，详见 `docs/STATUS.md`。

`integration/FullMain.lean` 提供复用另一份公开完整证明的最终衔接源码；这条依赖链尚未在本机完成全量重建，未纳入默认核验库。

## 文件

- `Smale5.lean` 与 `Smale5/`：已核验的 Lean 源码。
- `verification/`：源码哈希、121 个定理的完整清单和公理审计。
- `blueprint/`：形式化蓝图。
- `manuscript/main.tex`、`manuscript/main.pdf`：形式化改写稿。
- `docs/SOURCES.md`：公开计算来源和固定版本。
- `THIRD_PARTY_NOTICES.md`：上游定义和证明片段的归属说明。

仓库保存源码与证据。Lean、Mathlib 缓存、Archon 会话、计算机本地路径记录、下载归档和第三方完整源码在工作目录之外管理。
