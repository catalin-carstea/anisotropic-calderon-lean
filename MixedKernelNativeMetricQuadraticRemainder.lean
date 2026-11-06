import MixedKernelNativeJacobiBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric ConnectionError MetricOperator
open scoped ContDiff Topology

/-- Reassociate only the actual normal metric's signed radius, and subtract its zero jet. -/
def nativeMetricDeviationByRadius (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (a : (ℝ × (R3 × R3)) × ℝ) : R3 →L[ℝ] R3 :=
  conformalReferenceFramedNormalMetric S.g1 L P.Phi
    (a.1.1,((a.1.2.1,a.2),a.1.2.2)) - ContinuousLinearMap.id ℝ R3

/-- The remainder is the actual double derivative-average, defined before derivative orders. -/
def nativeMetricQuadraticRemainder (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (a : ReferenceEndpointVariables) : R3 →L[ℝ] R3 :=
  parameterHadamardDivision (parameterHadamardDivision (nativeMetricDeviationByRadius S L P))
    ((a.1,(a.2.1.1,a.2.2)),a.2.1.2)

/-- The quadratic remainder is genuinely smooth, including at signed radius zero. -/
theorem contDiff_nativeMetricQuadraticRemainder
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ContDiff ℝ ∞ (nativeMetricQuadraticRemainder S L P) := by
  have hData : ConformalReferenceFramedMetricData S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo := P.native_data.1.1
  rcases hData with ⟨_,_,_,_,_,hG,_,_⟩
  have hD : ContDiff ℝ ∞ (nativeMetricDeviationByRadius S L P) :=
    (hG.comp (contDiff_fst.fst.prodMk
      ((contDiff_fst.snd.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd.snd))).sub contDiff_const
  exact (contDiff_parameterHadamardDivision _ (contDiff_parameterHadamardDivision _ hD)).comp
    ((contDiff_fst.prodMk (contDiff_snd.fst.fst.prodMk contDiff_snd.snd)).prodMk contDiff_snd.fst.snd)

/-- Actual original zero jets yield the exact quadratic identity on the FULL closed center room. -/
theorem native_normal_metric_eq_id_add_radius_sq
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-P.y0‖ ≤ 4*P.rho) (r : ℝ) (z : R3)
    (hz : z ∈ closedBall (0 : R3) 2) :
    conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),z)) =
      ContinuousLinearMap.id ℝ R3 + r^2 • nativeMetricQuadraticRemainder S L P (lam,((y,r),z)) := by
  have hData : ConformalReferenceFramedMetricData S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo := P.native_data.1.1
  rcases hData with ⟨_,heps,_,_,_,hG,hRoom,_⟩
  have hsmall : 4*P.rho ≤ P.epsGeo := P.native_data.1.2.2.1
  have hj := hRoom lam hlam y (hy.trans hsmall) 0 (by simpa using heps.le) z hz
  have hz0 : nativeMetricDeviationByRadius S L P ((lam,(y,z)),0) = 0 := by
    change conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,0),z)) - _ = 0
    rw [hj.2.2.1,sub_self]
  have hfirst : HasDerivAt (fun s : ℝ => nativeMetricDeviationByRadius S L P ((lam,(y,z)),s)) 0 0 :=
    hj.2.2.2.1.sub_const (ContinuousLinearMap.id ℝ R3)
  have hD : ContDiff ℝ ∞ (nativeMetricDeviationByRadius S L P) :=
    (hG.comp (contDiff_fst.fst.prodMk
      ((contDiff_fst.snd.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd.snd))).sub contDiff_const
  have hh := radius_sq_smul_parameterHadamardDivision_two
    (nativeMetricDeviationByRadius S L P) hD (lam,(y,z)) r hz0 hfirst
  change conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),z)) - _ =
    r^2 • nativeMetricQuadraticRemainder S L P (lam,((y,r),z)) at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

/-- All finite joint remainder derivatives are bounded on the SAME fixed compact signed room. -/
theorem exists_nativeMetricQuadraticRemainder_compact_bounds
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
      ∀ a ∈ conformalReferenceFramedMetricRoom P.y0 (4*P.rho),
        ‖iteratedFDeriv ℝ j (nativeMetricQuadraticRemainder S L P) a‖ ≤ D := by
  intro N
  obtain ⟨D,hD,H⟩ := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (fun _ : Unit => nativeMetricQuadraticRemainder S L P)
    (conformalReferenceFramedMetricRoom P.y0 (4*P.rho))
    (isCompact_Icc.prod (((isCompact_closedBall _ _).prod isCompact_Icc).prod
      (isCompact_closedBall _ _)))
    (fun _ _ _ => (contDiff_nativeMetricQuadraticRemainder S L P).contDiffAt) N
  exact ⟨D,hD,fun j hj a ha => H j hj a ha ()⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
