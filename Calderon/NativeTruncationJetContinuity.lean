import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.Sobolev.W1p.LevelSet

/-! EXPANSION.json precedes this transparent exact pinned-proof partition. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E]

def posPartJet (z : Sobolev1Jet E) : Sobolev1Jet E :=
  if 0 < z.fst then z else 0

lemma norm_posPartJet_le (z : Sobolev1Jet E) :
    ‖posPartJet z‖ ≤ ‖z‖ := by
  by_cases hz : 0 < z.fst <;> simp [posPartJet, hz]

lemma continuousAt_posPartJet {z : Sobolev1Jet E}
    (hzero : z.fst = 0 → z = 0) : ContinuousAt posPartJet z := by
  rcases lt_trichotomy 0 z.fst with hpos | heq | hneg
  · have he : ∀ᶠ w in 𝓝 z, 0 < w.fst :=
      ((WithLp.continuous_fst 2 ℝ E).tendsto z).eventually (eventually_gt_nhds hpos)
    rw [ContinuousAt, posPartJet, ite_eq_left hpos]
    exact tendsto_id.congr' (he.mono fun w hw ↦ by simp [posPartJet, hw])
  · have hz := hzero heq.symm
    subst z
    simpa only [ContinuousAt, posPartJet, WithLp.zero_fst, lt_self_iff_false,
      ite_false] using squeeze_zero_norm norm_posPartJet_le tendsto_norm_zero
  · have he : ∀ᶠ w in 𝓝 z, w.fst < 0 :=
      ((WithLp.continuous_fst 2 ℝ E).tendsto z).eventually (eventually_lt_nhds hneg)
    rw [ContinuousAt, posPartJet, ite_eq_right (not_lt_of_gt hneg)]
    exact tendsto_const_nhds.congr' (he.mono fun w hw ↦ by
      simp [posPartJet, not_lt_of_gt hw])

def posPartAboveJet (k : ℝ) (z : Sobolev1Jet E) : Sobolev1Jet E :=
  posPartJet (z - WithLp.toLp 2 (k, 0))

lemma norm_posPartAboveJet_le {k : ℝ} (hk : 0 ≤ k) (z : Sobolev1Jet E) :
    ‖posPartAboveJet k z‖ ≤ ‖z‖ := by
  by_cases hz : k < z.fst
  · simp only [posPartAboveJet, posPartJet, WithLp.sub_fst, WithLp.toLp_fst,
      sub_pos.mpr hz, ite_true]
    rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    simp only [WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst, WithLp.toLp_snd,
      sub_zero, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hz.le),
      abs_of_nonneg (hk.trans hz.le)]
    gcongr
    exact sub_le_self _ hk
  · simp [posPartAboveJet, posPartJet, sub_pos, hz]

lemma continuousAt_posPartAboveJet (k : ℝ) {z : Sobolev1Jet E}
    (hzero : z.fst = k → z.snd = 0) : ContinuousAt (posPartAboveJet k) z := by
  have hz : (z - WithLp.toLp 2 (k, 0)).fst = 0 → z - WithLp.toLp 2 (k, 0) = 0 := by
    intro hx
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simpa only [WithLp.ofLp_fst, WithLp.zero_fst] using hx
    · simp only [WithLp.ofLp_snd, WithLp.sub_snd, WithLp.toLp_snd, sub_zero,
        WithLp.zero_snd]
      exact hzero (sub_eq_zero.mp (by simpa only [WithLp.sub_fst, WithLp.toLp_fst] using hx))
  have hshift : ContinuousAt (fun w : Sobolev1Jet E ↦ w - WithLp.toLp 2 (k, 0)) z :=
    continuousAt_id.sub continuousAt_const
  exact (continuousAt_posPartJet hz).comp
    (f := fun w : Sobolev1Jet E ↦ w - WithLp.toLp 2 (k, 0)) hshift

variable [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

lemma posPartAbove_coe_ae (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k)
    (u : W1p mu Omega p) :
    ⇑(W1p.posPartAbove hp hk u : Sobolev1JetLp mu Omega p) =ᵐ[mu.restrict Omega]
      fun x ↦ posPartAboveJet k ((u : Sobolev1JetLp mu Omega p) x) := by
  filter_upwards [W1p.value_apply_ae (W1p.posPartAbove hp hk u),
    W1p.gradient_apply_ae (W1p.posPartAbove hp hk u), W1p.value_apply_ae u,
    W1p.gradient_apply_ae u, W1p.value_posPartAbove_ae hp hk u,
    W1p.gradient_posPartAbove_ae hp hk u] with x hv hg huv hug hvp hgp
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp only [WithLp.ofLp_fst]
    rw [← hv, hvp]
    by_cases hx : k < W1p.value u x
    · simp [posPartAboveJet, posPartJet, ← huv, sub_pos, hx,
        max_eq_left (sub_nonneg.mpr hx.le)]
    · simp [posPartAboveJet, posPartJet, ← huv, sub_pos, hx,
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hx))]
  · simp only [WithLp.ofLp_snd]
    rw [← hg, hgp]
    by_cases hx : k < W1p.value u x <;>
      simp [posPartAboveJet, posPartJet, ← huv, ← hug, sub_pos, hx]

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.posPartJet
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.norm_posPartJet_le
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.continuousAt_posPartJet
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.posPartAboveJet
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.norm_posPartAboveJet_le
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.continuousAt_posPartAboveJet
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.posPartAbove_coe_ae
