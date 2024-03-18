#=
using Catlab.WiringDiagrams, Catlab.Graphics

import Convex, SCS
import TikzPictures

using Catlab.Theories

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
f, g = Hom(:f, A, B), Hom(:g, B, A);

to_tikz(f, labels=true)
=#


using Catlab.Graphs, Catlab.Graphics

g = cycle_graph(Graph, 3)
to_graphviz(g)
