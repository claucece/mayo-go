import numpy as np

# Define dimensions
o = 2
m = 4
n = o + m # 6

# Generate a random o-by-(n-o) matrix
O = np.random.uniform(-1, 1, (o, n - o))

print("Random o-by-(n-o) matrix O:")
print(O)

# Create the identity matrix I_o of size o
I_o = np.identity(o)

print("Identity Matrix (I_o):")
print(I_o)

# Concatenate O and I_o horizontally
T = np.hstack((O, I_o))

print("Matrix (O | I_o):")
print(T)

# Then, x_i will determine the terms
# P_i^(1) is an upper triangular matrix of size 4 × 4
# P_i^(1) = [a_{1_1}, a_{1,2}, a_{1,3}, a_{1,4}
#            0,     , a_{2,2}, a_{2,3}, a{2,4},
#            0,     , 0      , a_{3,3}, a{3,4},
#            0,       0       ,0      , a_{4,4},]


# P_i^(2) is a rectangular  matrix of size (n-o) x o = 4 x 2
# P_i^(2) = [b_{1_1}, b_{1,2},
#            b_{2,1, b_{2,2},
#            b_{3,1}, a{3,2},
#            b_{4,1}, a{4,2},]

# P_i^(3) is an upper triangular matrix of size 2 × 2
# P_i^(3) = [c_{1_1}, c_{1,2},
#            0,     , c_{2,2},]

# Hence, P_i:

# P_i =     [a_{1_1}, a_{1,2}, a_{1,3}, a_{1,4}, b_{1, 1}, b_{1, 2},
#            0,     , a_{2,2}, a_{2,3}, a{2,4},  b_{2, 1}, b_{2, 2},
#            0,     , 0      , a_{3,3}, a{3,4},  b_{3, 1}, b_{3, 2},
#            0,       0       ,0      , a_{4,4}, b_{4, 1}, b_{4, 2},
#            0      , 0       ,0      , 0       , c_{1_1}, c_{1,2},
#            0,       0       ,0      ,0        ,0       , c_{2,2},]

# For the variables n = 6, set:
# x = {x_1, x_2, x_3, x_4, x_5, x_6}

# Then: p_i(x) = x^{T}P_i x

# which is sum_i=1^6 sum_j=i^6 P_ij x_i x_j
