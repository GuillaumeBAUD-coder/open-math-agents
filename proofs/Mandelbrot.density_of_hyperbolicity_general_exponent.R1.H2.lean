import OMAReductions.R_Mandelbrot_density_of_hyperbolicity_general_exponent_R1
import Mathlib

theorem OMA.solution : OMA.R_Mandelbrot_density_of_hyperbolicity_general_exponent_R1.H2 := by
  intro n hn
  exact Mandelbrot.multibrotSet_eq hn
