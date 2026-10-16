# CASCADE — формальная верификация математики модели старения центриолей (Lean 4)

**Модель:** CASCADE (*Counter-based Asymmetric Stem-Cell Aging: Division Counters & Entropy Export*) —
модель организменного старения. **Файл:** `CASCADE.lean` (папка `CASCADE/lean/`) — компилируется `lake env lean CASCADE.lean`, **0 ошибок, 0 warnings**.
**Модель:** рукопись Tqemaladze (модель геометрического старения центриолей, в подготовке;
препринт-подача — preprints.org), `L_{n+1} = α·L_n + (1-α)·L_0 + μ + ε_n`, α ≈ 0.97.
⚠️ Это НЕ публикация на bioRxiv (статей на bioRxiv нет).

## Доказано машинно (namespace `Cascade`)
| Утверждение модели | Теорема в Lean |
|---|---|
| Closed form длины | `length_closed_form`: `L_n = L₀ + μ(1-αⁿ)/(1-α)` |
| Closed form дисперсии | `variance_closed_form`: `Var(L_n) = σ²(1-(α²)ⁿ)/(1-α²)` |
| Приращение дисперсии | `variance_succ_sub`: `Var(L_{n+1}) − Var(L_n) = σ²·(α²)ⁿ` |
| Приращение длины | `length_succ_sub`: `L_{n+1} − L_n = μ·αⁿ` |
| **Персистентность** (нет релаксации к норме) | `variance_mono`: дисперсия не убывает по n |
| **Accumulation / counter function** (геометрия считает деления) | `length_drift_strict_mono`: при μ>0, α>0 длина строго растёт с делением |
| **Конечное равновесие (mean)** | `length_tendsto`: `L_n → L₀ + μ/(1-α)` |
| **Конечное равновесие (variance)** | `variance_tendsto`: `Var(L_n) → σ²/(1-α²)` |

## Статус
- Закоммичено во внутренний репо (`5c1a31c7`).
- Опубликовано в `github.com/djabbat/PN-lean` (`PN/CentrioleAging.lean`, до переноса в `CASCADE/lean/CASCADE.lean`).
- Новизна: это **оригинальная модель пользователя**, впервые (в его проекте) верифицированная
  в proof-assistant'е — не пере-верификация классической теоремы, а формализация собственного
  количественного результата.

## Возможные следующие шаги
- Стохастическая часть: формальная асимптотика OU (мартингалы) — тяжелее, частично в mathlib.
- Публикация в README-артефакт/CITATION для цитирования вместе с bioRxiv-статьёй.
