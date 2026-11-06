import MixedKernelPhaseHeight
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Filter Metric
open scoped Topology ContDiff

/-- Shrinking the master room radius puts the actual inverse first chart and second
coordinates in any prescribed open neighbourhood. Product distances use the max norm. -/
theorem exists_chart_product_closedD_neighborhood
    {K1 K2 : Type*} [NormedAddCommGroup K1] [NormedAddCommGroup K2]
    (e1 : OpenPartialHomeomorph R3 (ℝ × K1)) (p1 : R3)
    (htarget : (0 : ℝ × K1) ∈ e1.target)
    (hinverse : e1.symm (0 : ℝ × K1) = p1)
    (V : Set (R3 × (ℝ × K2))) (hV : IsOpen V) (hVm : (p1,0) ∈ V) :
    ∃ r : ℝ, 0 < r ∧ ∀ l eps R : ℝ,
      0 < eps → l + 4 * eps ≤ r → R ≤ r →
      ∀ u1 ∈ (PhaseCoordinates.closedD l eps R : Set (ℝ × K1)),
      ∀ u2 ∈ (PhaseCoordinates.closedD l eps R : Set (ℝ × K2)),
        (e1.symm u1,u2) ∈ V := by
  have hInv : ContinuousAt e1.symm (0 : ℝ × K1) :=
    e1.continuousOn_symm.continuousAt (e1.open_target.mem_nhds htarget)
  have hH : ContinuousAt
      (fun z : (ℝ × K1) × (ℝ × K2) => (e1.symm z.1,z.2)) 0 :=
    (hInv.comp (f := fun z : (ℝ × K1) × (ℝ × K2) => z.1)
      (x := (0 : (ℝ × K1) × (ℝ × K2))) continuousAt_fst).prodMk continuousAt_snd
  have hH0 : (e1.symm (0 : ℝ × K1),(0 : ℝ × K2)) ∈ V := by
    rw [hinverse]
    exact hVm
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp
    (hH.preimage_mem_nhds (hV.mem_nhds hH0))
  refine ⟨delta/2,half_pos hdelta,fun l eps R heps hl hR u1 hu1 u2 hu2 => ?_⟩
  have hb1 := PhaseCoordinates.closedD_subset_big heps hl hR hu1
  have hb2 := PhaseCoordinates.closedD_subset_big heps hl hR hu2
  have hn1 : ‖u1‖ ≤ delta/2 := by
    rw [Prod.norm_def]
    exact max_le (by simpa only [Real.norm_eq_abs] using abs_le.mpr hb1.1)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hb1.2)
  have hn2 : ‖u2‖ ≤ delta/2 := by
    rw [Prod.norm_def]
    exact max_le (by simpa only [Real.norm_eq_abs] using abs_le.mpr hb2.1)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hb2.2)
  have hmem : (u1,u2) ∈ Metric.ball (0 : (ℝ × K1) × (ℝ × K2)) delta := by
    rw [Metric.mem_ball,dist_zero_right,Prod.norm_def]
    exact (max_le hn1 hn2).trans_lt (by linarith)
  exact hball hmem

/-- Positive native height derivatives imply monotonicity on every output-room height slice. -/
theorem monotone_phase_height_on_roomO
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (rho : R3 × R3 → ℝ) (e2 : OpenPartialHomeomorph R3 (ℝ × K))
    (x : R3) (l eps R : ℝ)
    (hQ : ∀ q ∈ (PhaseCoordinates.roomO l eps R : Set (ℝ × K)),
      ContDiffAt ℝ 2 (fun w : R3 × (ℝ × K) => rho (w.1,e2.symm w.2)) (x,q) ∧
      0 < (fderiv ℝ (fun w : R3 × (ℝ × K) => rho (w.1,e2.symm w.2)) (x,q))
        (0,(1,0))) :
    ∀ z ∈ Metric.ball (0 : K) (R/2),
      MonotoneOn (fun s : ℝ => rho (x,e2.symm (s,z))) (Ioo (-eps) (l+3*eps/2)) := by
  intro z hz
  let Q : R3 × (ℝ × K) → ℝ := fun w => rho (w.1,e2.symm w.2)
  have hD : ∀ s ∈ Ioo (-eps) (l+3*eps/2),
      HasDerivAt (fun t : ℝ => rho (x,e2.symm (t,z)))
        ((fderiv ℝ Q (x,(s,z))) (0,(1,0))) s := by
    intro s hs
    have hcurve : HasDerivAt (fun t : ℝ => (x,(t,z))) (0,(1,0)) s :=
      (hasDerivAt_const s x).prodMk ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))
    exact ((hQ (s,z) ⟨hs,hz⟩).1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s hcurve
  apply (strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt) ?_).monotoneOn
  intro s hs
  have hs' : s ∈ Ioo (-eps) (l+3*eps/2) := interior_subset hs
  rw [(hD s hs').deriv]
  exact (hQ (s,z) ⟨hs',hz⟩).2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
