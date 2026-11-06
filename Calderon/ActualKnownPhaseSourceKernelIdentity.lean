import Calderon.ActualRadiusTwoSourceMatchingKernelRows
import Calderon.ActualRadiusTwoKernelOffPoleClassicalEquation
import Calderon.LocalMetricPullbackDivergence
import Calderon.ActualSourceChartHarmonicColumns
import Calderon.CollaboratorUniqueContinuationProofOct17
import Calderon.CollaboratorLocalJetsCalcOct17
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ConnectionError MetricVolume MetricOperator

/-- A point cannot separate an open connected physical region in dimension three. -/
theorem isConnected_sdiff_singleton_of_isOpen_R3
    (W : Set R3) (hWopen : IsOpen W) (hWconnected : IsConnected W)
    (p : R3) (hp : p ∈ W) : IsConnected (W \ {p}) := by
  classical
  have hRank : 1 < Module.rank ℝ R3 := by
    rw [← Module.finrank_eq_rank]
    norm_num [R3]
  have hSmall (r : ℝ) (hr : 0 < r) : IsConnected (ball p r \ {p}) := by
    let e : OpenPartialHomeomorph R3 R3 := OpenPartialHomeomorph.univBall p r
    have hSource : e.source = Set.univ := OpenPartialHomeomorph.univBall_source p r
    have hTarget : e.target = ball p r := OpenPartialHomeomorph.univBall_target p hr
    have hZero : e (0 : R3) = p := OpenPartialHomeomorph.univBall_apply_zero p r
    have hImage : e '' ({(0 : R3)} : Set R3)ᶜ = ball p r \ {p} := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        have htSource : t ∈ e.source := hSource.symm ▸ Set.mem_univ t
        have h0Source : (0 : R3) ∈ e.source := hSource.symm ▸ Set.mem_univ (0 : R3)
        refine ⟨hTarget ▸ e.map_source htSource, ?_⟩
        intro heq
        have het : e t = e (0 : R3) := (mem_singleton_iff.mp heq).trans hZero.symm
        exact ht (mem_singleton_iff.mpr (e.injOn htSource h0Source het))
      · intro hz
        have hzTarget : z ∈ e.target := hTarget.symm ▸ hz.1
        refine ⟨e.symm z, ?_, e.right_inv hzTarget⟩
        intro hZeroInv
        have hzEq : z = p := (e.right_inv hzTarget).symm.trans
          ((congrArg e (mem_singleton_iff.mp hZeroInv)).trans hZero)
        exact hz.2 (mem_singleton_iff.mpr hzEq)
    have hConnected := isConnected_compl_singleton_of_one_lt_rank hRank (0 : R3)
    have hContinuous : Continuous e := OpenPartialHomeomorph.continuous_univBall p r
    simpa only [hImage] using hConnected.image e hContinuous.continuousOn
  obtain ⟨r, hr, hBallW⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds hp)
  let D : Set R3 := W \ {p}
  have hDopen : IsOpen D := hWopen.sdiff isClosed_singleton
  have hBallD : ball p r \ {p} ⊆ D := fun z hz => ⟨hBallW hz.1, hz.2⟩
  refine ⟨(hSmall r hr).nonempty.mono hBallD, ?_⟩
  intro u v hu hv hCover hDu hDv
  by_contra hNo
  let U : Set R3 := u ∩ D
  let V : Set R3 := v ∩ D
  have hUopen : IsOpen U := hu.inter hDopen
  have hVopen : IsOpen V := hv.inter hDopen
  have hDisjoint : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    exact hNo ⟨z, hzU.2, hzU.1, hzV.1⟩
  have hUVcover : D ⊆ U ∪ V := by
    intro z hz
    rcases hCover hz with hzu | hzv
    · exact Or.inl ⟨hzu, hz⟩
    · exact Or.inr ⟨hzv, hz⟩
  have hUn : U.Nonempty := by
    obtain ⟨z, hzD, hzu⟩ := hDu
    exact ⟨z, hzu, hzD⟩
  have hVn : V.Nonempty := by
    obtain ⟨z, hzD, hzv⟩ := hDv
    exact ⟨z, hzv, hzD⟩
  have hContr (a b : Set R3) (ha : IsOpen a) (hb : IsOpen b)
      (hab : Disjoint a b) (haD : a ⊆ D) (hbD : b ⊆ D)
      (hDab : D ⊆ a ∪ b) (han : a.Nonempty) (hbn : b.Nonempty)
      (hSide : ball p r \ {p} ⊆ a) : False := by
    have hWcover : W ⊆ (a ∪ ball p r) ∪ b := by
      intro z hz
      by_cases hzp : z = p
      · apply Or.inl
        apply Or.inr
        simpa only [hzp] using mem_ball_self hr
      · have hzD : z ∈ D := ⟨hz, fun h => hzp (mem_singleton_iff.mp h)⟩
        rcases hDab hzD with hza | hzb
        · exact Or.inl (Or.inl hza)
        · exact Or.inr hzb
    obtain ⟨za, hza⟩ := han
    obtain ⟨zb, hzb⟩ := hbn
    have hMeet := hWconnected.isPreconnected (a ∪ ball p r) b (ha.union isOpen_ball) hb hWcover
      ⟨za, (haD hza).1, Or.inl hza⟩ ⟨zb, (hbD hzb).1, hzb⟩
    obtain ⟨z, _hzW, hzA, hzB⟩ := hMeet
    rcases hzA with hza | hzBall
    · exact Set.disjoint_left.mp hab hza hzB
    · exact Set.disjoint_left.mp hab (hSide ⟨hzBall, (hbD hzB).2⟩) hzB
  have hSmallCover : ball p r \ {p} ⊆ U ∪ V := hBallD.trans hUVcover
  rcases IsPreconnected.subset_or_subset hUopen hVopen hDisjoint hSmallCover
      (hSmall r hr).isPreconnected with hSide | hSide
  · exact hContr U V hUopen hVopen hDisjoint (fun _ h => h.2) (fun _ h => h.2)
      hUVcover hUn hVn hSide
  · exact hContr V U hVopen hUopen hDisjoint.symm (fun _ h => h.2) (fun _ h => h.2)
      (fun z hz => (hUVcover hz).symm) hVn hUn hSide

/-- The same source rows agree throughout the existing physical known-side isometry region. -/
theorem eqOn_radiusTwoSourceKernel_rows_of_known_isometry_and_source_match
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (K1 K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G1 G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData1 : IsRadiusTwoSymmetricInverseSourceKernel g1 hg1 K1 G1)
    (hData2 : IsRadiusTwoSymmetricInverseSourceKernel g2 hg2 K2 G2)
    (W : Set R3) (hWopen : IsOpen W) (hWconnected : IsConnected W)
    (hWroom : W ⊆ (radiusTwoOpens : Set R3))
    (hSource : (fixedExteriorSourceOpens : Set R3) ⊆ W)
    (X : R3 → R3) (hXroom : ∀ p ∈ W, X p ∈ (radiusTwoOpens : Set R3))
    (hXsmooth : ContDiffOn ℝ ∞ X W) (hXinj : Set.InjOn X W)
    (hJac : ∀ p ∈ W, IsUnit (coordinateJacobianMatrix X p).det)
    (hIso : EqOn (pullbackMetric g2 X) g1 W)
    (hFix : ∀ z ∈ (fixedExteriorSourceOpens : Set R3), X z = z)
    (hMatch : ∀ p ∈ W,
      radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 p =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 (X p)) :
    ∀ p (hp : p ∈ W), ∀ z ∈ W, z ≠ p →
      G1 ⟨p, hWroom hp⟩ z = G2 ⟨X p, hXroom p hp⟩ (X z) := by
  classical
  intro p hp z hz hzp
  let p1 : (radiusTwoOpens : Set R3) := ⟨p, hWroom hp⟩
  let p2 : (radiusTwoOpens : Set R3) := ⟨X p, hXroom p hp⟩
  let D : Set R3 := W \ {p}
  let T2 : Set R3 := (radiusTwoOpens : Set R3) \ {X p}
  have hDopen : IsOpen D := hWopen.sdiff isClosed_singleton
  have hDconnected : IsConnected D :=
    isConnected_sdiff_singleton_of_isOpen_R3 W hWopen hWconnected p hp
  have hT2open : IsOpen T2 := radiusTwoOpens.isOpen.sdiff isClosed_singleton
  have hDroom : D ⊆ (radiusTwoOpens : Set R3) \ {(p : R3)} :=
    fun _ ht => ⟨hWroom ht.1, ht.2⟩
  have hXavoid : ∀ t ∈ D, X t ∈ T2 := by
    intro t ht
    refine ⟨hXroom t ht.1, ?_⟩
    intro htp
    exact ht.2 (mem_singleton_iff.mpr (hXinj ht.1 hp (mem_singleton_iff.mp htp)))
  have hRow1 := radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
    hreg hcalc g1 hg1 K1 G1 hData1 p1
  have hRow2 := radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
    hreg hcalc g2 hg2 K2 G2 hData2 p2
  let u1 : R3 → ℝ := G1 p1
  let u2 : R3 → ℝ := (G2 p2) ∘ X
  let A : R3 → Matrix (Fin 3) (Fin 3) ℝ := principalCoefficient g1
  have hA : ContDiff ℝ ∞ A := contDiff_principalCoefficient g1 hg1
  have hC1 : ContDiffOn ℝ ∞ u1 D := hRow1.1.mono hDroom
  have hC2 : ContDiffOn ℝ ∞ u2 D :=
    hRow2.1.comp (hXsmooth.mono diff_subset) hXavoid
  have hL1 : ∀ t ∈ D, divCoeffGrad A u1 t = 0 := by
    intro t ht
    have hN := hRow1.2 t (hDroom ht)
    change -divCoeffGrad A u1 t = 0 at hN
    exact neg_eq_zero.mp hN
  have hL2 : ∀ t ∈ D, divCoeffGrad A u2 t = 0 := by
    intro t ht
    have hNt := hRow2.2 (X t) (hXavoid t ht)
    have hZeroOriginal : coordinateFluxDivergence (metricDivergenceFlux g2 (G2 p2)) (X t) = 0 := by
      rw [nativeMetricDifferential_eq_neg_coordinateFluxDivergence] at hNt
      exact neg_eq_zero.mp hNt
    have hCov := coordinateFluxDivergence_pullbackMetric_of_contDiffOn
      g2 hg2.smooth hg2.posDef X (G2 p2) D T2 hDopen hT2open
      (hXsmooth.mono diff_subset) hRow2.1 t ht (hXavoid t ht) (hJac t ht.1)
    have hZeroPull : coordinateFluxDivergence
        (metricDivergenceFlux (pullbackMetric g2 X) u2) t = 0 := by
      exact hCov.trans ((congrArg (fun a : ℝ => |(coordinateJacobianMatrix X t).det| * a)
        hZeroOriginal).trans (mul_zero _))
    have hNativePull : Literature.nativeMetricDifferential (pullbackMetric g2 X) u2 t = 0 :=
      (nativeMetricDifferential_eq_neg_coordinateFluxDivergence (pullbackMetric g2 X) u2 t).trans
        ((congrArg Neg.neg hZeroPull).trans neg_zero)
    have hDivPull : divCoeffGrad (principalCoefficient (pullbackMetric g2 X)) u2 t = 0 := by
      change -divCoeffGrad (principalCoefficient (pullbackMetric g2 X)) u2 t = 0 at hNativePull
      exact neg_eq_zero.mp hNativePull
    have hCoeff : principalCoefficient (pullbackMetric g2 X) =ᶠ[𝓝 t] A := by
      filter_upwards [hWopen.mem_nhds ht.1] with s hs
      change Real.sqrt (((pullbackMetric g2 X) s).det) • ((pullbackMetric g2 X) s)⁻¹ =
        Real.sqrt ((g1 s).det) • (g1 s)⁻¹
      rw [hIso hs]
    exact (UCP.divCoeffGrad_congr hCoeff (EventuallyEq.refl (𝓝 t) u2)).symm.trans hDivPull
  let d : R3 → ℝ := u1 + (-1 : ℝ) • u2
  have hCd : ContDiffOn ℝ ∞ d D := hC1.add (hC2.const_smul (-1 : ℝ))
  have hLd : ∀ t ∈ D, divCoeffGrad A d t = 0 := by
    intro t ht
    have hAt : DifferentiableAt ℝ A t := hA.differentiable (by simp) t
    have hu1 : ContDiffAt ℝ 2 u1 t :=
      (hC1.contDiffAt (hDopen.mem_nhds ht)).of_le (by simp)
    have hu2 : ContDiffAt ℝ 2 u2 t :=
      (hC2.contDiffAt (hDopen.mem_nhds ht)).of_le (by simp)
    let v2 : R3 → ℝ := (-1 : ℝ) • u2
    have hv2 : ContDiffAt ℝ 2 v2 t := by
      change ContDiffAt ℝ 2 (fun s => (-1 : ℝ) • u2 s) t
      exact hu2.const_smul (-1 : ℝ)
    have hAdd : divCoeffGrad A (u1 + v2) t =
        divCoeffGrad A u1 t + divCoeffGrad A v2 t :=
      Regularity.Jets.divCoeffGrad_add (u := u1) (v := v2) hAt hu1 hv2
    have hScale : divCoeffGrad A v2 t = (-1 : ℝ) * divCoeffGrad A u2 t :=
      Regularity.Jets.divCoeffGrad_smul (u := u2) (-1 : ℝ) hAt hu2
    calc
      divCoeffGrad A d t = divCoeffGrad A u1 t + divCoeffGrad A v2 t := hAdd
      _ = divCoeffGrad A u1 t + (-1 : ℝ) * divCoeffGrad A u2 t :=
        congrArg (fun b : ℝ => divCoeffGrad A u1 t + b) hScale
      _ = 0 := by rw [hL1 t ht, hL2 t ht]; ring
  let S : Set R3 := (fixedExteriorSourceOpens : Set R3)
  let V0 : Set R3 := S \ ({p} ∪ {X p})
  have hSopen : IsOpen S := fixedExteriorSourceOpens.isOpen
  have hSconnected : IsConnected S := by
    change IsConnected (ball fixedExteriorSourceCenter (1/8 : ℝ))
    exact isConnected_ball (by norm_num)
  have hAvoidSecond (t : R3) (ht : t ∈ S) (htp : t ≠ p) : t ≠ X p := by
    intro heq
    exact htp (hXinj (hSource ht) hp ((hFix t ht).trans heq))
  have hV0n : V0.Nonempty := by
    by_cases hpS : p ∈ S
    · obtain ⟨t, htS, htp⟩ :=
        (isConnected_sdiff_singleton_of_isOpen_R3 S hSopen hSconnected p hpS).nonempty
      refine ⟨t, htS, ?_⟩
      intro hForbidden
      rcases hForbidden with hForbidden | hForbidden
      · exact htp hForbidden
      · exact hAvoidSecond t htS (fun h => htp (mem_singleton_iff.mpr h))
          (mem_singleton_iff.mp hForbidden)
    · obtain ⟨t, htS⟩ := fixedExteriorSourceOpens_nonempty
      have htp : t ≠ p := fun h => hpS (h ▸ htS)
      refine ⟨t, htS, ?_⟩
      intro hForbidden
      rcases hForbidden with hForbidden | hForbidden
      · exact htp (mem_singleton_iff.mp hForbidden)
      · exact hAvoidSecond t htS htp (mem_singleton_iff.mp hForbidden)
  have hV0open : IsOpen V0 := hSopen.sdiff (isClosed_singleton.union isClosed_singleton)
  have hV0D : V0 ⊆ D := by
    intro t ht
    exact ⟨hSource ht.1, fun h => ht.2 (Or.inl h)⟩
  have hSeedRows := eqOn_radiusTwoSourceKernel_rows_of_sourceEvaluationFamily_eq
    hreg hcalc g1 g2 hg1 hg2 K1 K2 G1 G2 hData1 hData2 p1 p2 (hMatch p hp)
  have hSeed : ∀ t ∈ V0, d t = 0 := by
    intro t ht
    have hEq := hSeedRows ht
    change G1 p1 t + (-1 : ℝ) * G2 p2 (X t) = 0
    rw [hFix t ht.1, hEq, neg_one_mul, add_neg_cancel]
  have hZero := uniqueContinuation D hDopen hDconnected A hA.contDiffOn
    (fun t _ => principalCoefficient_posDef g1 hg1 t) d hCd hLd
    V0 hV0open hV0n hV0D hSeed z ⟨hz, fun h => hzp (mem_singleton_iff.mp h)⟩
  have hSub : G1 p1 z - G2 p2 (X z) = 0 := by
    simpa only [d, u1, u2, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_apply, neg_one_mul, sub_eq_add_neg] using hZero
  exact sub_eq_zero.mp hSub

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.isConnected_sdiff_singleton_of_isOpen_R3
#print axioms OAI.AnisotropicCalderon.ExteriorSource.eqOn_radiusTwoSourceKernel_rows_of_known_isometry_and_source_match
