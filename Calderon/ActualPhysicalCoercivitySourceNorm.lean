import Calderon.WeightedPhysicalCoercivityGraphClosure
import Calderon.ActualUniformWeightedBaseBudget
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral

theorem norm_referenceBaseLift_le_of_finite_physical_graph_coercivity
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L q c:ℝ) (hc:0 < c)
    (U:ℕ→R3→SphereL2) (u:R3→SphereL2) (V:ℕ→R3→SphereL2) (v:R3→SphereL2)
    (hU:∀ n,Continuous (U n)) (hu:Continuous u) (hV:∀ n,Continuous (V n)) (hv:Continuous v)
    (hUc:∀ n,HasCompactSupport (U n)) (huc:HasCompactSupport u)
    (hVc:∀ n,HasCompactSupport (V n)) (hvc:HasCompactSupport v)
    (hSource:Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily g L (q,y)*‖U n y-u y‖^2) atTop (𝓝 0))
    (hOutput:Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily g L (q,y)*‖V n y-v y‖^2) atTop (𝓝 0))
    (hFinite:∀ n:ℕ,c*(∫ y,referenceDensityFamily g L (q,y)*‖U n y‖^2) ≤
      ∫ y,referenceDensityFamily g L (q,y)*‖V n y‖^2):
    ‖referenceBaseLift g hg L q u hu huc‖ ≤ ‖referenceBaseLift g hg L q v hv hvc‖/Real.sqrt c := by
  have h:=weighted_physical_coercive_bound_of_graph_limits g hg L q c U u V v hU hu hV hv hUc huc hVc hvc hSource hOutput hFinite
  have hs:0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsq:(Real.sqrt c*‖referenceBaseLift g hg L q u hu huc‖)^2 ≤ ‖referenceBaseLift g hg L q v hv hvc‖^2 := by
    rw [mul_pow,Real.sq_sqrt hc.le,norm_sq_referenceBaseLift,norm_sq_referenceBaseLift]
    exact h
  have hNorm:Real.sqrt c*‖referenceBaseLift g hg L q u hu huc‖ ≤ ‖referenceBaseLift g hg L q v hv hvc‖ :=
    (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg _)) (norm_nonneg _)).mp hsq
  exact (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hNorm)

theorem exists_uniform_same_cutoff_source_norm_shift
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L B:ℝ):
    ∃ C:ℝ,0 < C ∧ ∀ q∈Icc (0:ℝ) 1,∀ (chi:R3→ℝ) (hchi:Continuous chi) (hchic:HasCompactSupport chi),
      tsupport chi⊆closedBall (0:R3) B → range chi⊆Icc (0:ℝ) 1 →
      ∀ (U:R3→SphereL2) (hU:Continuous U) (one:SphereL2),
      ‖referenceBaseLift g hg L q (fun y => chi y • U y) (hchi.smul hU) hchic.smul_right‖ ≤
        ‖referenceBaseLift g hg L q (fun y => chi y • (U y-one)) (hchi.smul (hU.sub continuous_const)) hchic.smul_right‖+C*‖one‖ := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_referenceBaseLift_bound_of_supported_pointwise_bound g hg L B
  refine ⟨C,hC,?_⟩
  intro q hq chi hchi hchic hSupport hRange U hU one
  let K:R3→SphereL2 := fun y => chi y • one
  have hK:Continuous K := hchi.smul continuous_const
  have hKc:HasCompactSupport K := hchic.smul_right
  have hKS:tsupport K⊆closedBall (0:R3) B := (tsupport_smul_subset_left chi (fun _:R3 => one)).trans hSupport
  have hKB:∀ y∈closedBall (0:R3) B,‖K y‖ ≤ ‖one‖ := by
    intro y hy
    dsimp only [K]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hRange (Set.mem_range_self y)).1]
    exact (mul_le_mul_of_nonneg_right (hRange (Set.mem_range_self y)).2 (norm_nonneg one)).trans_eq (one_mul _)
  have hKN:=HC q hq K hK hKc hKS ‖one‖ (norm_nonneg _) hKB
  let Z:R3→SphereL2 := fun y => chi y • U y
  have hZ:Continuous Z := hchi.smul hU
  have hZc:HasCompactSupport Z := hchic.smul_right
  have hSub:(fun y => Z y-K y)=(fun y => chi y • (U y-one)) := by funext y;exact (smul_sub _ _ _).symm
  have hEq:=referenceBaseLift_sub g hg L q Z K hZ hK hZc hKc
  have hN:‖referenceBaseLift g hg L q Z hZ hZc-referenceBaseLift g hg L q K hK hKc‖=
      ‖referenceBaseLift g hg L q (fun y => chi y • (U y-one)) (hchi.smul (hU.sub continuous_const)) hchic.smul_right‖ := by
    simpa only [hSub] using congrArg norm hEq.symm
  have hTri:=norm_add_le (referenceBaseLift g hg L q Z hZ hZc-referenceBaseLift g hg L q K hK hKc)
    (referenceBaseLift g hg L q K hK hKc)
  rw [sub_add_cancel,hN] at hTri
  exact hTri.trans (add_le_add_right hKN _)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
