import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory TopologicalSpace NormedSpace Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

lemma ae_equal_def0 {E : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MetricSpace E] [IsFiniteMeasure μ] (g h : α → E) (y z : E): g =ᵐ[μ] h ↔ μ ({ x : α | (dist (g x) (h x)) > 0 }) = 0 := by
  constructor
  · intros h1 ε hε
    rw [] at h1
    sorry
  · sorry

lemma ae_equal_def {E : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MetricSpace E] [IsFiniteMeasure μ] (g h : α → E) (y z : E): g =ᵐ[μ] h ↔ ∀ ε>0, μ ({ x : α | (dist (g x) (h x)) > ε }) = 0 := by
  constructor
  · intros h1 ε hε
    rw [] at h1
    sorry
  · sorry


theorem tendstoInMeasure_ae_unique {α : Type u_1} {E : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MetricSpace E] {f : ℕ → α → E} {g h : α → E} [IsFiniteMeasure μ] (hg : TendstoInMeasure μ f Filter.atTop g) (hh : TendstoInMeasure μ f Filter.atTop h) : g =ᵐ[μ] h := by
  rw [TendstoInMeasure] at hg hh


  intro A B

  sorry
