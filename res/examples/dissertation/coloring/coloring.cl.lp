{asg(V,C)} :- vtx(V); color(C).
           :- asg(V, C1); asg(V, C2); C1 != C2.
           :- vtx(V); not asg(V, C) : color(C).
           :- asg(V1, C); asg(V2, C); edge(V1, V2).
