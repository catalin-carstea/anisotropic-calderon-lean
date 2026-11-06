import Calderon.SpatialHessianFiniteJets

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
open MetricVolume

/-- Restricting a jointly smooth germ to its spatial second coordinate does not
increase any iterated Fréchet derivative norm for the standard product norm. -/
theorem norm_iteratedFDeriv_prod_slice_snd_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (ℝ × R3) → V) (lam : ℝ) (x : R3)
    (hf : ContDiffAt ℝ ∞ f (lam, x)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y : R3 => f (lam, y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (lam, x)‖ := by
  obtain ⟨T, hTnhds, hfT⟩ := hf.contDiffOn (m := (n : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨U, hUT, hU, hxU⟩ := _root_.mem_nhds_iff.mp hTnhds
  have hfU : ContDiffOn ℝ (n : ℕ∞ω) f U := hfT.mono hUT
  let b : ℝ × R3 := (lam, 0)
  let g : R3 →ₗᵢ[ℝ] ℝ × R3 := LinearIsometry.inr ℝ ℝ R3
  let H : (ℝ × R3) → V := fun z => f (z + b)
  let S : Set (ℝ × R3) := (fun z => z + b) ⁻¹' U
  have hS : IsOpen S := hU.preimage (continuous_id.add continuous_const)
  have hH : ContDiffOn ℝ (n : ℕ∞ω) H S :=
    hfU.comp (contDiff_id.add contDiff_const).contDiffOn (fun z hz => hz)
  let l : R3 →L[ℝ] ℝ × R3 := g.toContinuousLinearMap
  have hPre : IsOpen (l ⁻¹' S) := hS.preimage l.continuous
  have hg : l x ∈ S := by simpa [S, l, g, b] using hxU
  have hWithin := l.iteratedFDerivWithin_comp_right (f := H) (s := S) (x := x)
    hH hS.uniqueDiffOn hPre.uniqueDiffOn hg (i := n) le_rfl
  have hLeft : iteratedFDerivWithin ℝ n (H ∘ (l : R3 → ℝ × R3)) (l ⁻¹' S) x =
      iteratedFDeriv ℝ n (H ∘ (l : R3 → ℝ × R3)) x :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := H ∘ (l : R3 → ℝ × R3)) n hPre) hg
  have hRight : iteratedFDerivWithin ℝ n H S (l x) = iteratedFDeriv ℝ n H (l x) :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := H) n hS) hg
  rw [hLeft, hRight] at hWithin
  have hShift : iteratedFDeriv ℝ n H (l x) = iteratedFDeriv ℝ n f (lam, x) := by
    simpa [H, l, g, b] using iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) n b (l x)
  rw [hShift] at hWithin
  have hOrd : iteratedFDeriv ℝ n (fun y : R3 => f (lam, y)) x =
      (iteratedFDeriv ℝ n f (lam, x)).compContinuousLinearMap
        (fun _ : Fin n => g.toContinuousLinearMap) := by
    simpa [H, Function.comp_def, l, g, b] using hWithin
  rw [hOrd]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => g)

/-- Finite-Pi assembly of smooth functions has iterated derivative norm bounded
by the sum of the component derivative norms. -/
theorem norm_iteratedFDeriv_pi_le_sum
    {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (g : E → ι → V) (x : E) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n g x‖ ≤
      ∑ k : ι, ‖iteratedFDeriv ℝ n (fun y => g y k) x‖ := by
  have hPi : iteratedFDeriv ℝ n g x =
      ContinuousMultilinearMap.pi (fun k : ι =>
        iteratedFDeriv ℝ n (fun y => g y k) x) := by
    ext m k
    have hProj := (ContinuousLinearMap.proj k : (ι → V) →L[ℝ] V).iteratedFDeriv_comp_left
      hg (i := n) (by simp)
    have hEval := congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) V => D m) hProj
    exact hEval.symm
  rw [hPi, ContinuousMultilinearMap.opNorm_pi]
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun k _ => norm_nonneg _))).2 ?_
  intro k
  exact Finset.single_le_sum
    (fun j _ => norm_nonneg (iteratedFDeriv ℝ n (fun y => g y j) x))
    (Finset.mem_univ k)

/-- The coordinate Hessian is smooth as a matrix-valued germ. -/
theorem contDiffAt_coordinateHessian
    (f : R3 → ℝ) (x : R3) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (fun y : R3 => (fun i j : Fin 3 =>
      fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) : Mat)) x := by
  have hDf := hf.fderiv_right (m := ∞) (by simp)
  have hB := hDf.fderiv_right (m := ∞) (by simp)
  exact hB.continuousLinearMap_comp bilinearCoordinateMap

/-- The spatial derivative norm of a finite family of coordinate Hessians is
bounded by the sum of the corresponding scalar derivatives, with constant one. -/
theorem norm_iteratedFDeriv_coordinateHessian_family_le_sum
    (f : Fin 5 → R3 → ℝ) (x : R3)
    (hf : ∀ k : Fin 5, ContDiffAt ℝ ∞ (f k) x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n
      (fun y : R3 => (fun k : Fin 5 => (fun i j : Fin 3 =>
        fderiv ℝ (fderiv ℝ (f k)) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) : Mat))) x‖ ≤
      ∑ k : Fin 5, ‖iteratedFDeriv ℝ (n + 2) (f k) x‖ := by
  have hSmooth : ContDiffAt ℝ ∞
      (fun y : R3 => (fun k : Fin 5 => (fun i j : Fin 3 =>
        fderiv ℝ (fderiv ℝ (f k)) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) : Mat))) x :=
    contDiffAt_pi.2 (fun k => contDiffAt_coordinateHessian (f k) x (hf k))
  apply (norm_iteratedFDeriv_pi_le_sum _ x hSmooth n).trans
  exact Finset.sum_le_sum (fun k _ => norm_iteratedFDeriv_coordinateHessian_le (f k) x (hf k) n)

end OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
