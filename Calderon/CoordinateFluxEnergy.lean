import Calderon.CoordinateWeakIntegration

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem energyFormH1_eq_sum_coordinateFlux_inner
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u v : BallH1)
    (q : Fin 3 → Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (hq : ∀ i j, q i j =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => a x i j * (TauCeti.W1p.gradient u x) j) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a 0 0 u v =
      ∑ i : Fin 3, ∑ j : Fin 3, ⟪q i j, unitBallCoordinateGradientL i v⟫_ℝ := by
  let z := fun (i j : Fin 3) (x : R3) => ⟪q i j x, unitBallCoordinateGradientL i v x⟫_ℝ
  have hi (i j : Fin 3) : Integrable (z i j)
      ((volume : Measure R3).restrict ballOpens) :=
    L2.integrable_inner (𝕜 := ℝ) (q i j) (unitBallCoordinateGradientL i v)
  have hf : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i j : Fin 3,
      q i j x = a x i j * (TauCeti.W1p.gradient u x) j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hq i j
  have hg : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      unitBallCoordinateGradientL i v x = (TauCeti.W1p.gradient v x) i :=
    ae_all_iff.mpr fun i => unitBallCoordinateGradientL_ae i v
  have hs : (∫ x in ballOpens, ∑ i, ∑ j, z i j x) =
      ∑ i, ∑ j, ∫ x in ballOpens, z i j x := by
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hi i j)
  calc
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a 0 0 u v =
        ∫ x in ballOpens, ∑ i, ∑ j, z i j x := by
      rw [TauCeti.PDE.energyFormH1_def]
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hx hy
      simp only [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.jetField_apply,
        TauCeti.PDE.driftForm_apply, TauCeti.PDE.massForm_apply, Pi.zero_apply, inner_zero_left, zero_mul,
        add_zero, TauCeti.PDE.matrixBilinearForm_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [z, RCLike.inner_apply, conj_trivial]
      rw [hx i j, hy i]
    _ = ∑ i, ∑ j, ∫ x in ballOpens, z i j x := hs
    _ = ∑ i, ∑ j, ⟪q i j, unitBallCoordinateGradientL i v⟫_ℝ := by
      simp only [L2.inner_def, z]

end OAI.AnisotropicCalderon.DirichletFamily
