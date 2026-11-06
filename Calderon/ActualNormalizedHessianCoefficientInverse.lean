import Calderon.MetricHessianTestEquiv
import Calderon.CompactInverseDerivativeBounds
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Linarith
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Distributions Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature MetricVolume ConformalDepth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_normalized_hessianCoefficient_uniform_inverse
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (v : Fin 5 → R3 → ℝ)
    (r : ℝ) (hr : 0 < r)
    (hv : ∀ k : Fin 5, ContDiffOn ℝ ∞ (v k) (ball (0 : R3) r))
    (hJets : ∀ k : Fin 5, fderiv ℝ (fderiv ℝ (v k)) 0 =
      matrixJetBilinear (traceFreeHessianMatrix ((g 0)⁻¹) k))
    (L : ℝ) (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ Mat := Matrix.normedSpace
    letI : NormedAddCommGroup (Mat →L[ℝ] Mat) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (Mat →L[ℝ] Mat) :=
      ContinuousLinearMap.toNormedSpace
    let H : (ℝ × R3) → Fin 5 → Mat := fun t k i j =>
      fderiv ℝ (fderiv ℝ (v k)) (t.1 • t.2)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    let gamma : (ℝ × R3) → Mat := fun t =>
      Real.exp (-2 * L * referenceCoordinateDepth t.2) •
        g (t.1 • t.2)
    ∃ A : (ℝ × R3) → (Mat →L[ℝ] Mat),
      (∀ t : ℝ × R3, ∀ Z : Mat,
        A t Z =
          ![![matrixContractionL (H t 0) Z,
              matrixContractionL (H t 1) Z,
              matrixContractionL (H t 2) Z],
            ![matrixContractionL (H t 3) Z,
              matrixContractionL (H t 4) Z,
              matrixContractionL (gamma t) Z],
            ![Z 0 1 - Z 1 0, Z 0 2 - Z 2 0, Z 1 2 - Z 2 1]]) ∧
      ∃ (eta C : ℝ) (U : Set (ℝ × R3)),
        0 < eta ∧ eta ≤ 1 ∧ 0 ≤ C ∧ IsOpen U ∧
        (Icc (-eta) eta ×ˢ K ⊆ U) ∧
        (∀ t ∈ U, t.1 • t.2 ∈ ball (0 : R3) (r / 2)) ∧
        ContDiffOn ℝ ∞ A U ∧
        (∀ t ∈ U, (A t).IsInvertible) ∧
        ContDiffOn ℝ ∞ (fun t => (A t).inverse) U ∧
        (∀ n : ℕ, n ≤ N → ∀ t ∈ Icc (-eta) eta ×ˢ K,
          ‖iteratedFDeriv ℝ n A t‖ ≤ C) ∧
        (∀ n : ℕ, n ≤ N → ∀ t ∈ Icc (-eta) eta ×ˢ K,
          ‖iteratedFDeriv ℝ n (fun t => (A t).inverse) t‖ ≤ C) := by
  classical
  letI : NormedAddCommGroup Mat := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ Mat := Matrix.normedSpace
  letI : NormedAddCommGroup (Mat →L[ℝ] Mat) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Mat →L[ℝ] Mat) :=
    ContinuousLinearMap.toNormedSpace
  let H : (ℝ × R3) → Fin 5 → Mat := fun t k i j =>
    fderiv ℝ (fderiv ℝ (v k)) (t.1 • t.2)
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  let gamma : (ℝ × R3) → Mat := fun t =>
    Real.exp (-2 * L * referenceCoordinateDepth t.2) •
      g (t.1 • t.2)
  let entryC : Fin 3 → Fin 3 → (Mat →L[ℝ] ℝ) := fun a b =>
    ({ toFun := fun Z : Mat => Z a b
       map_add' := fun X Y => rfl
       map_smul' := fun c Z => rfl } : Mat →ₗ[ℝ] ℝ).toContinuousLinearMap
  let rankOne : Fin 3 → Fin 3 → Fin 3 → Fin 3 → (Mat →L[ℝ] Mat) :=
    fun i j a b => (entryC a b).smulRight (coordinateMatrixUnit i j)
  let coeff : (ℝ × R3) → Fin 3 → Fin 3 → Mat := fun t =>
    ![![H t 0, H t 1, H t 2],
      ![H t 3, H t 4, gamma t],
      ![coordinateMatrixUnit 0 1 - coordinateMatrixUnit 1 0,
        coordinateMatrixUnit 0 2 - coordinateMatrixUnit 2 0,
        coordinateMatrixUnit 1 2 - coordinateMatrixUnit 2 1]]
  let A : (ℝ × R3) → (Mat →L[ℝ] Mat) := fun t =>
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
      coeff t i j a b • rankOne i j a b
  have hRows (t : ℝ × R3) (Z : Mat) :
      A t Z =
        ![![matrixContractionL (H t 0) Z,
            matrixContractionL (H t 1) Z,
            matrixContractionL (H t 2) Z],
          ![matrixContractionL (H t 3) Z,
            matrixContractionL (H t 4) Z,
            matrixContractionL (gamma t) Z],
          ![Z 0 1 - Z 1 0, Z 0 2 - Z 2 0, Z 1 2 - Z 2 1]] := by
    have hRankOneApply (i j a b : Fin 3) (X : Mat) (u w : Fin 3) :
        rankOne i j a b X u w =
          X a b * (if u = i ∧ w = j then 1 else 0) := rfl
    have hScalarCoordinate (C : Fin 3 → Fin 3 → Mat) (X : Mat) (u w : Fin 3) :
        (∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
          C i j a b • rankOne i j a b) X u w =
          matrixContractionL (C u w) X := by
      simp only [sum_apply, smul_apply, Matrix.smul_apply, smul_eq_mul,
        hRankOneApply]
      change (∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        C i j a b * (X a b * (if u = i ∧ w = j then 1 else 0))) =
          ∑ a : Fin 3, ∑ b : Fin 3, C u w a b * X a b
      rw [Finset.sum_eq_single u]
      · rw [Finset.sum_eq_single w]
        · have h : u = u ∧ w = w := ⟨rfl, rfl⟩
          rw [ite_eq_left h]
          simp only [mul_one]
        · intro j hj hjw
          have h : ¬ (u = u ∧ w = j) := fun h => hjw h.2.symm
          rw [ite_eq_right h]
          simp only [mul_zero, Finset.sum_const_zero]
        · intro hw
          exact False.elim (hw (Finset.mem_univ w))
      · intro i hi hiu
        apply Finset.sum_eq_zero
        intro j hj
        have h : ¬ (u = i ∧ w = j) := fun h => hiu h.1.symm
        rw [ite_eq_right h]
        simp only [mul_zero, Finset.sum_const_zero]
      · intro hu
        exact False.elim (hu (Finset.mem_univ u))
    have hUnitContraction (a b : Fin 3) (X : Mat) :
        matrixContractionL (coordinateMatrixUnit a b) X = X a b := by
      change (∑ i : Fin 3, ∑ j : Fin 3,
        (if i = a ∧ j = b then 1 else 0) * X i j) = X a b
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · have h : a = a ∧ b = b := ⟨rfl, rfl⟩
          rw [ite_eq_left h]
          simp only [one_mul]
        · intro j hj hjb
          have h : ¬ (a = a ∧ j = b) := fun h => hjb h.2
          rw [ite_eq_right h]
          simp only [zero_mul]
        · intro hb
          exact False.elim (hb (Finset.mem_univ b))
      · intro i hi hia
        apply Finset.sum_eq_zero
        intro j hj
        have h : ¬ (i = a ∧ j = b) := fun h => hia h.1
        rw [ite_eq_right h]
        simp only [zero_mul]
      · intro ha
        exact False.elim (ha (Finset.mem_univ a))
    have hSubContraction (X Y Z : Mat) :
        matrixContractionL (X - Y) Z =
          matrixContractionL X Z - matrixContractionL Y Z := by
      change (∑ a : Fin 3, ∑ b : Fin 3, (X a b - Y a b) * Z a b) =
        (∑ a : Fin 3, ∑ b : Fin 3, X a b * Z a b) -
          (∑ a : Fin 3, ∑ b : Fin 3, Y a b * Z a b)
      simp only [sub_mul, Finset.sum_sub_distrib]
    ext i j
    change (∑ u : Fin 3, ∑ w : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
      coeff t u w a b • rankOne u w a b) Z i j = _
    rw [hScalarCoordinate]
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · change matrixContractionL
        (coordinateMatrixUnit 0 1 - coordinateMatrixUnit 1 0) Z = Z 0 1 - Z 1 0
      rw [hSubContraction, hUnitContraction, hUnitContraction]
    · change matrixContractionL
        (coordinateMatrixUnit 0 2 - coordinateMatrixUnit 2 0) Z = Z 0 2 - Z 2 0
      rw [hSubContraction, hUnitContraction, hUnitContraction]
    · change matrixContractionL
        (coordinateMatrixUnit 1 2 - coordinateMatrixUnit 2 1) Z = Z 1 2 - Z 2 1
      rw [hSubContraction, hUnitContraction, hUnitContraction]
  let scale : (ℝ × R3) → R3 := fun t => t.1 • t.2
  let O0 : Set (ℝ × R3) := scale ⁻¹' ball (0 : R3) (r / 2)
  have hScale : ContDiff ℝ ∞ scale := contDiff_fst.smul contDiff_snd
  have hO0 : IsOpen O0 := isOpen_ball.preimage hScale.continuous
  have hMaps : MapsTo scale O0 (ball (0 : R3) r) := by
    intro t ht
    exact (ball_subset_ball (by linarith : r / 2 ≤ r)) ht
  have hHH (k : Fin 5) : ContDiffOn ℝ ∞
      (fun t : ℝ × R3 => fderiv ℝ (fderiv ℝ (v k)) (scale t)) O0 :=
    (((hv k).fderiv_of_isOpen (m := (∞ : ℕ∞ω)) isOpen_ball (by simp)).fderiv_of_isOpen
      (m := (∞ : ℕ∞ω)) isOpen_ball (by simp)).comp hScale.contDiffOn hMaps
  have hH (k : Fin 5) (a b : Fin 3) :
      ContDiffOn ℝ ∞ (fun t => H t k a b) O0 :=
    ((hHH k).clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hExp : ContDiff ℝ ∞ (fun t : ℝ × R3 =>
      Real.exp (-2 * L * referenceCoordinateDepth t.2)) :=
    (contDiff_const.mul (contDiff_referenceCoordinateDepth.comp contDiff_snd)).exp
  have hGamma (a b : Fin 3) : ContDiffOn ℝ ∞ (fun t => gamma t a b) O0 := by
    have hPulledEntry : ContDiffOn ℝ ∞
        (fun t : ℝ × R3 =>
          g (scale t) a b) O0 := by
      simpa only [Function.comp_def] using
        ((hg.smooth a b).comp hScale).contDiffOn
    have hScalarProduct : ContDiffOn ℝ ∞
        (fun t : ℝ × R3 =>
          Real.exp (-2 * L * referenceCoordinateDepth t.2) •
            g (scale t) a b) O0 :=
      hExp.contDiffOn.smul hPulledEntry
    simpa only [gamma, Matrix.smul_apply, scale] using hScalarProduct
  have hCoeff (i j a b : Fin 3) : ContDiffOn ℝ ∞ (fun t => coeff t i j a b) O0 := by
    fin_cases i <;> fin_cases j
    · exact hH 0 a b
    · exact hH 1 a b
    · exact hH 2 a b
    · exact hH 3 a b
    · exact hH 4 a b
    · exact hGamma a b
    · exact contDiffOn_const
    · exact contDiffOn_const
    · exact contDiffOn_const
  have hRankSmooth (i j a b : Fin 3) :
      ContDiff ℝ ∞ (fun c : ℝ => c • rankOne i j a b) :=
    (ContinuousLinearMap.toSpanSingleton ℝ (rankOne i j a b)).contDiff
  have hA : ContDiffOn ℝ ∞ A O0 :=
    ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ =>
        (hRankSmooth i j a b).comp_contDiffOn (hCoeff i j a b)))))
  let a : Mat := (g 0)⁻¹
  have haSym (i j : Fin 3) : a i j = a j i := by
    simpa only [a, star_trivial] using ((hg.posDef 0).inv.isHermitian.apply j i)
  have ha22 : a 2 2 ≠ 0 := ne_of_gt ((hg.posDef 0).inv.diag_pos (i := (2 : Fin 3)))
  have hHZero (y : R3) (k : Fin 5) :
      H (0, y) k = traceFreeHessianMatrix a k := by
    ext i j
    change fderiv ℝ (fderiv ℝ (v k)) ((0 : ℝ) • y)
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = _
    rw [zero_smul, hJets k]
    exact matrixJetBilinear_coordinateVector _ i j
  have hMul : g 0 * a = (1 : Mat) :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg.posDef 0).det_pos.ne')
  have hTrace : (∑ i : Fin 3, ∑ j : Fin 3, g 0 i j * a i j) = (3 : ℝ) := by
    calc
      _ = ∑ i : Fin 3, (g 0 * a) i i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro j hj
        rw [haSym j i]
      _ = 3 := by rw [hMul]; norm_num
  have hContract (y : R3) :
      (∑ i : Fin 3, ∑ j : Fin 3, gamma (0, y) i j * a i j) ≠ 0 := by
    have hG0 : gamma (0, y) =
        Real.exp (-2 * L * referenceCoordinateDepth y) • g 0 := by
      simp only [gamma, zero_smul]
    rw [hG0]
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hTrace]
    exact mul_ne_zero (Real.exp_ne_zero _) (by norm_num)
  have hAZero (y : R3) : (A (0, y)).IsInvertible := by
    have hEq : A (0, y) = (hessianTestL a (gamma (0, y))).toContinuousLinearMap := by
      ext Z i j
      rw [hRows]
      simp only [hHZero]
      rfl
    rw [hEq]
    change ((hessianTestEquiv a (gamma (0, y)) haSym ha22 (hContract y)).toContinuousLinearEquiv :
      Mat →L[ℝ] Mat).IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv
  let U : Set (ℝ × R3) := O0 ∩ A ⁻¹' {T : Mat →L[ℝ] Mat | T.IsInvertible}
  have hU : IsOpen U := hA.continuousOn.isOpen_inter_preimage hO0
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hZero : ({(0 : ℝ)} : Set ℝ) ×ˢ K ⊆ U := by
    rintro ⟨lam, y⟩ ⟨hlam, hy⟩
    have hlam0 : lam = 0 := Set.mem_singleton_iff.mp hlam
    subst lam
    refine ⟨?_, hAZero y⟩
    change (0 : ℝ) • y ∈ ball (0 : R3) (r / 2)
    simpa only [zero_smul, Metric.mem_ball, dist_self] using half_pos hr
  obtain ⟨u, w, hu, hw, h0u, hKw, hProduct⟩ :=
    generalized_tube_lemma isCompact_singleton hK hU hZero
  have h0uPoint : (0 : ℝ) ∈ u := h0u (by simp)
  have h0uNhds : u ∈ 𝓝 (0 : ℝ) := hu.mem_nhds h0uPoint
  obtain ⟨d, hd, hdu⟩ := Metric.mem_nhds_iff.mp h0uNhds
  let eta : ℝ := min 1 (d / 2)
  have hEta : 0 < eta := lt_min zero_lt_one (half_pos hd)
  have hEta1 : eta ≤ 1 := min_le_left _ _
  have hEtad : eta ≤ d / 2 := min_le_right _ _
  have hStrip : Icc (-eta) eta ×ˢ K ⊆ U := by
    intro t ht
    apply hProduct
    refine ⟨hdu ?_, hKw ht.2⟩
    have hAbs : |t.1| ≤ eta := abs_le.mpr ht.1
    have hLt : |t.1| < d := lt_of_le_of_lt hAbs (by linarith)
    simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using hLt
  have hAU : ContDiffOn ℝ ∞ A U := hA.mono inter_subset_left
  have hInvert : ∀ t ∈ U, (A t).IsInvertible := fun t ht => ht.2
  have hInverse : ContDiffOn ℝ ∞ (fun t => (A t).inverse) U :=
    contDiffOn_banachInverseFamily A U hAU hInvert
  have hCompact : IsCompact (Icc (-eta) eta ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨CA, hCA, hBoundA⟩ := exists_compact_iteratedFDeriv_bound A
    (Icc (-eta) eta ×ˢ K) hCompact
    (fun t ht => hAU.contDiffAt (hU.mem_nhds (hStrip ht))) N
  obtain ⟨CI, hCI, hBoundI⟩ := exists_compact_iteratedFDeriv_bound (fun t => (A t).inverse)
    (Icc (-eta) eta ×ˢ K) hCompact
    (fun t ht => hInverse.contDiffAt (hU.mem_nhds (hStrip ht))) N
  refine ⟨A, hRows, eta, CA + CI, U, hEta, hEta1, add_nonneg hCA hCI,
    hU, hStrip, ?_, hAU, hInvert, hInverse, ?_, ?_⟩
  · intro t ht
    exact ht.1
  · intro n hn t ht
    exact (hBoundA n hn t ht).trans (le_add_of_nonneg_right hCI)
  · intro n hn t ht
    exact (hBoundI n hn t ht).trans (le_add_of_nonneg_left hCA)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
