restart
R = QQ[x_0..x_6]
I = ideal {x_0*x_6,x_3*x_4,x_2*x_3,x_1*x_2,x_3*x_4*x_6,x_0*x_2*x_5,x_0*x_1*x_3}
res I
1,6,11,8,2
  1, 1
1,7,12,8,2

restart
R = ZZ/32003[x_1..x_6]
I = ideal apply(6, i -> x_(i+1)^2)
S = R/I
J = sub(ideal take(random flatten entries basis(2,S),6),R)
S = R/(I+J)
J = J + sub(ideal take(random flatten entries basis(3,S),6),R)
gbTrace = 2
minimalBetti J

--- seems to be a good example:
J = ideal {x_4*x_5, x_3*x_6, x_1*x_2, x_5*x_6, x_1*x_3, x_2*x_5, x_2*x_4*x_6, x_1*x_4*x_6, x_2*x_3*x_4}
res(J, FastNonminimal => true)

--- example that didn't pan out (no non-minimal syzygies)
B1 = {x_1*x_2, x_1*x_3, x_1*x_4, x_1*x_5, x_1*x_6, x_2*x_3, x_2*x_4*x_5,x_2*x_4*x_6}
  
B2 = {x_2*e_(1,2),
      x_2*e_(1,3),
      x_3*e_(1,3),
      x_2*e_(1,4),
      x_3*e_(1,4),
      x_4*e_(1,4),
      x_2*e_(1,5),
      x_3*e_(1,5),
      x_4*e_(1,5),
      x_5*e_(1,5),
      x_1*e_(1,6),
      x_1*e_(1,7),
      x_3*e_(1,7),
      x_1*e_(1,8),
      x_3*e_(1,8),
      x_5*e_(1,8)}
  
B3 = { x_2*e_(2,3),
       x_2*e_(2,5),
       x_2*e_(2,6),
       x_3*e_(2,6),
       x_2*e_(2,8),
       x_2*e_(2,9),
       x_3*e_(2,9),
       x_2*e_(2,10),
       x_3*e_(2,10),
       x_4*e_(2,10),
       x_1*e_(2,13),
       x_1*e_(2,15),
       x_1*e_(2,16),
       x_3*e_(2,16)}

B4 = { x_2*e_(3,4),
       x_2*e_(3,7),
       x_2*e_(3,9),
       x_2*e_(3,10),
       x_3*e_(3,10),
       x_1*e_(3,14)}

B5 = { x_2*e_(4,5) }
   
gbTrace = 2
minimalBetti J

restart
R = ZZ/32003[x_6,x_5,x_4,x_3,x_2,x_1]
R = ZZ/32003[x_1..x_6]
J = ideal {x_4*x_5, x_3*x_6, x_1*x_2, x_5*x_6, x_1*x_3, x_2*x_5, x_2*x_4*x_6, x_1*x_4*x_6, x_2*x_3*x_4}
J = ideal {x_1*x_2, x_1*x_3, x_2*x_5, x_4*x_5, x_3*x_6, x_5*x_6, x_2*x_3*x_4, x_1*x_4*x_6, x_2*x_4*x_6}
-- correct one!
J = ideal {x_5*x_6, x_4*x_6, x_2*x_5, x_1*x_4, x_2*x_3, x_1*x_2, x_1*x_3*x_6, x_3*x_4*x_5, x_1*x_3*x_5}
phi = map(R,R,reverse gens R)
K = phi J
gensJ = sort J_*
gensJ = J_*
netList apply(#gensJ, i -> (sub((ideal take(gensJ, i)),R) : ideal (gensJ#(i))))
gbTrace = 2
minimalBetti(J)
(ideal x_5*x_6 : ideal x_4*x_5)
res(J, FastNonminimal=>true)
K = ideal gens R
res(K, FastNonminimal=>true)

restart
R = ZZ/32003[x_0..x_5]
I = ideal {x_2*x_4*x_5, x_0*x_4*x_5, x_2*x_3*x_5, x_1*x_3*x_5, x_0*x_1*x_5,
           x_1*x_3*x_4, x_0*x_3*x_4, x_1*x_2*x_4, x_0*x_2*x_3, x_0*x_1*x_2}
I_*
sort I_*
res(I, FastNonminimal=>true)
gensI = I_*
netList apply(#gensI, i -> (sub((ideal take(gensI, i)),R) : ideal (gensI#(i))))

restart
R = ZZ/32003[x_1..x_6]
J = ideal {x_4*x_5, x_3*x_6, x_1*x_2, x_5*x_6, x_1*x_3, x_2*x_5, x_2*x_4*x_6, x_1*x_4*x_6, x_2*x_3*x_4}
phi = map(R,R,reverse gens R)
K = phi J
gensK = sort K_*
netList apply(#gensK, i -> (sub((ideal take(gensK, i)),R) : ideal (gensK#(i))))
gbTrace = 2
minimalBetti(K)
res(K, FastNonminimal=>true)

restart
R = ZZ/32003[x,y,z]
J = ideal {x^2,x*y,x*z}
phi = map(R,R,reverse gens R)
K = phi J
gensK = sort K_*
netList apply(#gensK, i -> (sub((ideal take(gensK, i)),R) : ideal (gensK#(i))))
gbTrace = 2
minimalBetti(K)
res(K, FastNonminimal=>true)

restart
R = ZZ/32003[m,x,y,z]
I = ideal {x^2,x*y*z,x*m^2,y^3}
gensI = sort I_*
netList apply(#gensI, i -> (sub((ideal take(gensI, i)),R) : ideal (gensI#(i))))
gbTrace = 2
minimalBetti(I)
C = res(I, FastNonminimal => true)

restart
R = ZZ/32003[x,y,z]
I = ideal {x^2,x*y,x*z}
gensI = sort I_*
netList apply(#gensI, i -> (sub((ideal take(gensI, i)),R) : ideal (gensI#(i))))
gbTrace = 2
minimalBetti(I)
C = res(I, FastNonminimal => true)

