/*
 * This software is a cooperative product of The MathWorks and the National
 * Institute of Standards and Technology (NIST) which has been released to the
 * public domain. Neither The MathWorks nor NIST assumes any responsibility
 * whatsoever for its use by other parties, and makes no guarantees, expressed
 * or implied, about its quality, reliability, or any other characteristic.
 */

/*
 * Matrix.cpp
 * Copyright (C) 1999 The Mathworks and NIST and 2005 University of Waikato,
 *               Hamilton, New Zealand
 *
 */

// package weka.core.matrix;

// import weka.core.RevisionHandler;
// import weka.core.RevisionUtils;
// import weka.core.Utils;

// import java.io.BufferedReader;
// import java.io.LineNumberReader;
// import java.io.PrintWriter;
// import java.io.Reader;
// import java.io.Serializable;
// import java.io.StreamTokenizer;
// import java.io.StringReader;
// import java.io.StringWriter;
// import java.io.Writer;
// import java.text.DecimalFormat;
// import java.text.DecimalFormatSymbols;
// import java.text.NumberFormat;
// import java.util.Locale;
// import java.util.StringTokenizer;
#include <cmath> 
#include <string> 
#include <iostream> 

using namespace std; 

/**
 * Jama = Java Matrix class.
 * <P>
 * The Java Matrix Class provides the fundamental operations of numerical linear
 * algebra.  Various constructors create Matrices from two dimensional arrays of
 * double precision floating point numbers.  Various "gets" and "sets" provide
 * access to submatrices and matrix elements.  Several methods implement basic
 * matrix arithmetic, including matrix addition and multiplication, matrix
 * norms, and element-by-element array operations.  Methods for reading and
 * printing matrices are also included.  All the operations in this version of
 * the Matrix Class involve real matrices.  Complex matrices may be handled in a
 * future version.
 * <P>
 * Five fundamental matrix decompositions, which consist of pairs or triples of
 * matrices, permutation vectors, and the like, produce results in five
 * decomposition classes.  These decompositions are accessed by the Matrix class
 * to compute solutions of simultaneous linear equations, determinants, inverses
 * and other matrix functions.  The five decompositions are:
 * <P>
 * <UL>
 *    <LI>Cholesky Decomposition of symmetric, positive definite matrices.
 *    <LI>LU Decomposition of rectangular matrices.
 *    <LI>QR Decomposition of rectangular matrices.
 *    <LI>Singular Value Decomposition of rectangular matrices.
 *    <LI>Eigenvalue Decomposition of both symmetric and nonsymmetric square matrices.
 * </UL>
 * <DL>
 * <DT><B>Example of use:</B></DT>
 * <P>
 * <DD>Solve a linear system A x = b and compute the residual norm, ||b - A x||.
 * <P><PRE>
 *       double[][] vals = {{1.,2.,3},{4.,5.,6.},{7.,8.,10.}};
 *       Matrix A = new Matrix(vals);
 *       Matrix b = Matrix.random(3,1);
 *       Matrix x = A.solve(b);
 *       Matrix r = A.times(x).minus(b);
 *       double rnorm = r.normInf();
 * </PRE></DD>
 * </DL>
 * <p/>
 * Adapted from the <a href="http://math.nist.gov/javanumerics/jama/" target="_blank">JAMA</a> package. Additional methods are tagged with the 
 * <code>@author</code> tag.
 *
 * @author The Mathworks and NIST 
 * @author Fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.8 $
 */
class Matrix : public Cloneable, public Serializable, public RevisionHandler {
protected: 
  /** 
   * Array for internal storage of elements.
   * @serial internal array storage.
   */
  double[][] A;

  /** 
   * Row and column dimensions.
   * @serial row dimension.
   * @serial column dimension.
   */
  int m, n;

private: 
  /** 
   * Check if size(A) == size(B) 
   */
  private void checkMatrixDimensions(Matrix B) {
    if (B.m != m || B.n != n) {
      throw new IllegalArgumentException("Matrix dimensions must agree.");
    }
  }

public: 
  /** 
   * Construct an m-by-n matrix of zeros. 
   * @param m    Number of rows.
   * @param n    Number of colums.
   */
  Matrix(int m, int n) {
    this.m = m;
    this.n = n;
    A = new double[m][n];
  }

  /** 
   * Construct an m-by-n constant matrix.
   * @param m    Number of rows.
   * @param n    Number of colums.
   * @param s    Fill the matrix with this scalar value.
   */
  Matrix(int m, int n, double s) {
    this.m = m;
    this.n = n;
    A = new double[m][n];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        A[i][j] = s;
      }
    }
  }

  /** 
   * Construct a matrix from a 2-D array.
   * @param A    Two-dimensional array of doubles.
   * @throws  IllegalArgumentException All rows must have the same length
   * @see        #constructWithCopy
   */
  Matrix(double[][] A) {
    m = A.length;
    n = A[0].length;
    for (int i = 0; i < m; i++) {
      if (A[i].length != n) {
        throw new IllegalArgumentException("All rows must have the same length.");
      }
    }
    this.A = A;
  }

  /** 
   * Construct a matrix quickly without checking arguments.
   * @param A    Two-dimensional array of doubles.
   * @param m    Number of rows.
   * @param n    Number of colums.
   */
  Matrix(double[][] A, int m, int n) {
    this.A = A;
    this.m = m;
    this.n = n;
  }

  /** 
   * Construct a matrix from a one-dimensional packed array
   * @param vals One-dimensional array of doubles, packed by columns (ala
   * Fortran).
   * @param m    Number of rows.
   * @throws  IllegalArgumentException Array length must be a multiple of m.
   */
  Matrix(double vals[], int m) {
    this.m = m;
    n = (m != 0 ? vals.length/m : 0);
    if (m*n != vals.length) {
      throw new IllegalArgumentException("Array length must be a multiple of m.");
    }
    A = new double[m][n];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        A[i][j] = vals[i+j*m];
      }
    }
  }

  /**
   * Reads a matrix from a reader. The first line in the file should
   * contain the number of rows and columns. Subsequent lines
   * contain elements of the matrix.
   * (FracPete: taken from old weka.core.Matrix class)
   *
   * @param     r the reader containing the matrix
   * @throws    Exception if an error occurs
   * @see       #write(Writer)
   */
  Matrix(Reader r) throws Exception {
    LineNumberReader lnr = new LineNumberReader(r);
    string line;
    int currentRow = -1;

    while ((line = lnr.readLine()) != null) {

      // Comments
      if (line.startsWith("%"))  
        continue;
      
      StringTokenizer st = new StringTokenizer(line);
      // Ignore blank lines
      if (!st.hasMoreTokens())  
        continue;

      if (currentRow < 0) {
        int rows = Integer.parseInt(st.nextToken());
        if (!st.hasMoreTokens())
          throw new Exception("Line " + lnr.getLineNumber() 
              + ": expected number of columns");

        int cols = Integer.parseInt(st.nextToken());
        A = new double[rows][cols];
        m = rows;
        n = cols;
        currentRow++;
        continue;

      } 
      else {
        if (currentRow == getRowDimension())
          throw new Exception("Line " + lnr.getLineNumber() 
              + ": too many rows provided");

        for (int i = 0; i < getColumnDimension(); i++) {
          if (!st.hasMoreTokens())
            throw new Exception("Line " + lnr.getLineNumber() 
                + ": too few matrix elements provided");

          set(currentRow, i, Double.valueOf(st.nextToken()).doubleValue());
        }
        currentRow++;
      }
    }

    if (currentRow == -1)
      throw new Exception("Line " + lnr.getLineNumber() 
          + ": expected number of rows");
    else if (currentRow != getRowDimension())
      throw new Exception("Line " + lnr.getLineNumber() 
          + ": too few rows provided");
  }

  /** 
   * Construct a matrix from a copy of a 2-D array.
   * @param A    Two-dimensional array of doubles.
   * @throws  IllegalArgumentException All rows must have the same length
   */
  static Matrix constructWithCopy(double[][] A) {
    int m = A.length;
    int n = A[0].length;
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      if (A[i].length != n) {
        throw new IllegalArgumentException
          ("All rows must have the same length.");
      }
      for (int j = 0; j < n; j++) {
        C[i][j] = A[i][j];
      }
    }
    return X;
  }

  /** 
   * Make a deep copy of a matrix
   */
  Matrix copy() {
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = A[i][j];
      }
    }
    return X;
  }

  /** 
   * Clone the Matrix object.
   */
  Object clone() {
    return this.copy();
  }

  /** 
   * Access the internal two-dimensional array.
   * @return     Pointer to the two-dimensional array of matrix elements.
   */
  double[][] getArray() {
    return A;
  }

  /** 
   * Copy the internal two-dimensional array.
   * @return     Two-dimensional array copy of matrix elements.
   */
  double[][] getArrayCopy() {
    double[][] C = new double[m][n];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = A[i][j];
      }
    }
    return C;
  }

  /** 
   * Make a one-dimensional column packed copy of the internal array.
   * @return     Matrix elements packed in a one-dimensional array by columns.
   */
  double[] getColumnPackedCopy() {
    double[] vals = new double[m*n];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        vals[i+j*m] = A[i][j];
      }
    }
    return vals;
  }

  /** 
   * Make a one-dimensional row packed copy of the internal array.
   * @return     Matrix elements packed in a one-dimensional array by rows.
   */
  double[] getRowPackedCopy() {
    double[] vals = new double[m*n];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        vals[i*n+j] = A[i][j];
      }
    }
    return vals;
  }

  /** 
   * Get row dimension.
   * @return     m, the number of rows.
   */
  int getRowDimension() {
    return m;
  }

  /** 
   * Get column dimension.
   * @return     n, the number of columns.
   */
  int getColumnDimension() {
    return n;
  }

  /** 
   * Get a single element.
   * @param i    Row index.
   * @param j    Column index.
   * @return     A(i,j)
   * @throws  ArrayIndexOutOfBoundsException
   */
  double get(int i, int j) {
    return A[i][j];
  }

  /** 
   * Get a submatrix.
   * @param i0   Initial row index
   * @param i1   Final row index
   * @param j0   Initial column index
   * @param j1   Final column index
   * @return     A(i0:i1,j0:j1)
   * @throws  ArrayIndexOutOfBoundsException Submatrix indices
   */
  Matrix getMatrix(int i0, int i1, int j0, int j1) {
    Matrix X = new Matrix(i1-i0+1,j1-j0+1);
    double[][] B = X.getArray();
    try {
      for (int i = i0; i <= i1; i++) {
        for (int j = j0; j <= j1; j++) {
          B[i-i0][j-j0] = A[i][j];
        }
      }
    } catch(ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException("Submatrix indices");
    }
    return X;
  }

  /** 
   * Get a submatrix.
   * @param r    Array of row indices.
   * @param c    Array of column indices.
   * @return     A(r(:),c(:))
   * @throws  ArrayIndexOutOfBoundsException Submatrix indices
   */
  Matrix getMatrix(int[] r, int[] c) {
    Matrix X = new Matrix(r.length,c.length);
    double[][] B = X.getArray();
    try {
      for (int i = 0; i < r.length; i++) {
        for (int j = 0; j < c.length; j++) {
          B[i][j] = A[r[i]][c[j]];
        }
      }
    } catch(ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException("Submatrix indices");
    }
    return X;
  }

  /** 
   * Get a submatrix.
   * @param i0   Initial row index
   * @param i1   Final row index
   * @param c    Array of column indices.
   * @return     A(i0:i1,c(:))
   * @throws  ArrayIndexOutOfBoundsException Submatrix indices
   */
  Matrix getMatrix(int i0, int i1, int[] c) {
    Matrix X = new Matrix(i1-i0+1,c.length);
    double[][] B = X.getArray();
    try {
      for (int i = i0; i <= i1; i++) {
        for (int j = 0; j < c.length; j++) {
          B[i-i0][j] = A[i][c[j]];
        }
      }
    } catch(ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException("Submatrix indices");
    }
    return X;
  }

  /** 
   * Get a submatrix.
   * @param r    Array of row indices.
   * @param j0   Initial column index
   * @param j1   Final column index
   * @return     A(r(:),j0:j1)
   * @throws  ArrayIndexOutOfBoundsException Submatrix indices
   */
  Matrix getMatrix(int[] r, int j0, int j1) {
    Matrix X = new Matrix(r.length,j1-j0+1);
    double[][] B = X.getArray();
    try {
      for (int i = 0; i < r.length; i++) {
        for (int j = j0; j <= j1; j++) {
          B[i][j-j0] = A[r[i]][j];
        }
      }
    } catch(ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException("Submatrix indices");
    }
    return X;
  }

  /** 
   * Set a single element.
   * @param i    Row index.
   * @param j    Column index.
   * @param s    A(i,j).
   * @throws  ArrayIndexOutOfBoundsException
   */
  void set(int i, int j, double s) {
    A[i][j] = s;
  }

  /** 
   * Set a submatrix.
   * @param i0   Initial row index
   * @param i1   Final row index
   * @param j0   Initial column index
   * @param j1   Final column index
   * @param X    A(i0:i1,j0:j1)
   * @throws  ArrayIndexOutOfBoundsException Submatrix indices
   */
  void setMatrix(int i0, int i1, int j0, int j1, Matrix X) {
    try {
      for (int i = i0; i <= i1; i++) {
        for (int j = j0; j <= j1; j++) {
          A[i][j] = X.get(i-i0,j-j0);
        }
      }
    } catch(ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException("Submatrix indices");
    }
  }

  /** 
   * Set a submatrix.
   * @param r    Array of row indices.
   * @param c    Array of column indices.
   * @param X    A(r(:),c(:))
   * @throws  ArrayIndexOutOfBoundsException Submatrix indices
   */
  void setMatrix(int[] r, int[] c, Matrix X) {
    try {
      for (int i = 0; i < r.length; i++) {
        for (int j = 0; j < c.length; j++) {
          A[r[i]][c[j]] = X.get(i,j);
        }
      }
    } catch(ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException("Submatrix indices");
    }
  }

  /** 
   * Set a submatrix.
   * @param r    Array of row indices.
   * @param j0   Initial column index
   * @param j1   Final column index
   * @param X    A(r(:),j0:j1)
   * @throws  ArrayIndexOutOfBoundsException Submatrix indices
   */
  void setMatrix(int[] r, int j0, int j1, Matrix X) {
    try {
      for (int i = 0; i < r.length; i++) {
        for (int j = j0; j <= j1; j++) {
          A[r[i]][j] = X.get(i,j-j0);
        }
      }
    } catch(ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException("Submatrix indices");
    }
  }

  /** 
   * Set a submatrix.
   * @param i0   Initial row index
   * @param i1   Final row index
   * @param c    Array of column indices.
   * @param X    A(i0:i1,c(:))
   * @throws  ArrayIndexOutOfBoundsException Submatrix indices
   */
  void setMatrix(int i0, int i1, int[] c, Matrix X) {
    try {
      for (int i = i0; i <= i1; i++) {
        for (int j = 0; j < c.length; j++) {
          A[i][c[j]] = X.get(i-i0,j);
        }
      }
    } catch(ArrayIndexOutOfBoundsException e) {
      throw new ArrayIndexOutOfBoundsException("Submatrix indices");
    }
  }
  
  /**
   * Returns true if the matrix is symmetric.
   * (FracPete: taken from old weka.core.Matrix class)
   *
   * @return boolean true if matrix is symmetric.
   */
  boolean isSymmetric() {
    int nr = A.length, nc = A[0].length;
    if (nr != nc)
      return false;

    for (int i = 0; i < nc; i++) {
      for (int j = 0; j < i; j++) {
        if (A[i][j] != A[j][i])
          return false;
      }
    }
    return true;
  }

  /**
   * returns whether the matrix is a square matrix or not.
   *
   * @return true if the matrix is a square matrix
   */
  boolean isSquare() {
    return (getRowDimension() == getColumnDimension());
  }

  /** 
   * Matrix transpose.
   * @return    A'
   */
  Matrix transpose() {
    Matrix X = new Matrix(n,m);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[j][i] = A[i][j];
      }
    }
    return X;
  }

  /** 
   * One norm
   * @return    maximum column sum.
   */
  double norm1() {
    double f = 0;
    for (int j = 0; j < n; j++) {
      double s = 0;
      for (int i = 0; i < m; i++) {
        s += abs(A[i][j]);
      }
      f = max(f,s);
    }
    return f;
  }

  /** 
   * Two norm
   * @return    maximum singular value.
   */
  double norm2() {
    return (new SingularValueDecomposition(this).norm2());
  }

  /** 
   * Infinity norm
   * @return    maximum row sum.
   */
  double normInf() {
    double f = 0;
    for (int i = 0; i < m; i++) {
      double s = 0;
      for (int j = 0; j < n; j++) {
        s += abs(A[i][j]);
      }
      f = max(f,s);
    }
    return f;
  }

  /** 
   * Frobenius norm
   * @return    sqrt of sum of squares of all elements.
   */
  double normF() {
    double f = 0;
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        f = Maths.hypot(f,A[i][j]);
      }
    }
    return f;
  }

  /**  
   * Unary minus
   * @return    -A
   */
  Matrix uminus() {
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = -A[i][j];
      }
    }
    return X;
  }

  /** 
   * C = A + B
   * @param B    another matrix
   * @return     A + B
   */
  Matrix plus(Matrix B) {
    checkMatrixDimensions(B);
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = A[i][j] + B.A[i][j];
      }
    }
    return X;
  }

  /** 
   * A = A + B
   * @param B    another matrix
   * @return     A + B
   */
  Matrix plusEquals(Matrix B) {
    checkMatrixDimensions(B);
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        A[i][j] = A[i][j] + B.A[i][j];
      }
    }
    return this;
  }

  /** 
   * C = A - B
   * @param B    another matrix
   * @return     A - B
   */
  Matrix minus(Matrix B) {
    checkMatrixDimensions(B);
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = A[i][j] - B.A[i][j];
      }
    }
    return X;
  }

  /** 
   * A = A - B
   * @param B    another matrix
   * @return     A - B
   */
  Matrix minusEquals(Matrix B) {
    checkMatrixDimensions(B);
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        A[i][j] = A[i][j] - B.A[i][j];
      }
    }
    return this;
  }

  /** 
   * Element-by-element multiplication, C = A.*B
   * @param B    another matrix
   * @return     A.*B
   */
  Matrix arrayTimes(Matrix B) {
    checkMatrixDimensions(B);
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = A[i][j] * B.A[i][j];
      }
    }
    return X;
  }

  /** 
   * Element-by-element multiplication in place, A = A.*B
   * @param B    another matrix
   * @return     A.*B
   */
  Matrix arrayTimesEquals(Matrix B) {
    checkMatrixDimensions(B);
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        A[i][j] = A[i][j] * B.A[i][j];
      }
    }
    return this;
  }

  /** 
   * Element-by-element right division, C = A./B
   * @param B    another matrix
   * @return     A./B
   */
  Matrix arrayRightDivide(Matrix B) {
    checkMatrixDimensions(B);
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = A[i][j] / B.A[i][j];
      }
    }
    return X;
  }

  /** 
   * Element-by-element right division in place, A = A./B
   * @param B    another matrix
   * @return     A./B
   */
  Matrix arrayRightDivideEquals(Matrix B) {
    checkMatrixDimensions(B);
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        A[i][j] = A[i][j] / B.A[i][j];
      }
    }
    return this;
  }

  /** 
   * Element-by-element left division, C = A.\B
   * @param B    another matrix
   * @return     A.\B
   */
  Matrix arrayLeftDivide(Matrix B) {
    checkMatrixDimensions(B);
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = B.A[i][j] / A[i][j];
      }
    }
    return X;
  }

  /** 
   * Element-by-element left division in place, A = A.\B
   * @param B    another matrix
   * @return     A.\B
   */
  Matrix arrayLeftDivideEquals(Matrix B) {
    checkMatrixDimensions(B);
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        A[i][j] = B.A[i][j] / A[i][j];
      }
    }
    return this;
  }

  /** 
   * Multiply a matrix by a scalar, C = s*A
   * @param s    scalar
   * @return     s*A
   */
  Matrix times(double s) {
    Matrix X = new Matrix(m,n);
    double[][] C = X.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        C[i][j] = s*A[i][j];
      }
    }
    return X;
  }

  /** 
   * Multiply a matrix by a scalar in place, A = s*A
   * @param s    scalar
   * @return     replace A by s*A
   */
  Matrix timesEquals(double s) {
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        A[i][j] = s*A[i][j];
      }
    }
    return this;
  }

  /** 
   * Linear algebraic matrix multiplication, A * B
   * @param B    another matrix
   * @return     Matrix product, A * B
   * @throws  IllegalArgumentException Matrix inner dimensions must agree.
   */
  Matrix times(Matrix B) {
    if (B.m != n) {
      throw new IllegalArgumentException("Matrix inner dimensions must agree.");
    }
    Matrix X = new Matrix(m,B.n);
    double[][] C = X.getArray();
    double[] Bcolj = new double[n];
    for (int j = 0; j < B.n; j++) {
      for (int k = 0; k < n; k++) {
        Bcolj[k] = B.A[k][j];
      }
      for (int i = 0; i < m; i++) {
        double[] Arowi = A[i];
        double s = 0;
        for (int k = 0; k < n; k++) {
          s += Arowi[k]*Bcolj[k];
        }
        C[i][j] = s;
      }
    }
    return X;
  }

  /** 
   * LU Decomposition
   * @return     LUDecomposition
   * @see LUDecomposition
   */
  LUDecomposition lu() {
    return new LUDecomposition(this);
  }

  /** 
   * QR Decomposition
   * @return     QRDecomposition
   * @see QRDecomposition
   */
  QRDecomposition qr() {
    return new QRDecomposition(this);
  }

  /** 
   * Cholesky Decomposition
   * @return     CholeskyDecomposition
   * @see CholeskyDecomposition
   */
  CholeskyDecomposition chol() {
    return new CholeskyDecomposition(this);
  }

  /** 
   * Singular Value Decomposition
   * @return     SingularValueDecomposition
   * @see SingularValueDecomposition
   */
  SingularValueDecomposition svd() {
    return new SingularValueDecomposition(this);
  }

  /** 
   * Eigenvalue Decomposition
   * @return     EigenvalueDecomposition
   * @see EigenvalueDecomposition
   */
  EigenvalueDecomposition eig() {
    return new EigenvalueDecomposition(this);
  }

  /** 
   * Solve A*X = B
   * @param B    right hand side
   * @return     solution if A is square, least squares solution otherwise
   */
  Matrix solve(Matrix B) {
    return (m == n ? (new LUDecomposition(this)).solve(B) :
        (new QRDecomposition(this)).solve(B));
  }

  /** 
   * Solve X*A = B, which is also A'*X' = B'
   * @param B    right hand side
   * @return     solution if A is square, least squares solution otherwise.
   */
  Matrix solveTranspose(Matrix B) {
    return transpose().solve(B.transpose());
  }

  /** 
   * Matrix inverse or pseudoinverse
   * @return     inverse(A) if A is square, pseudoinverse otherwise.
   */
  Matrix inverse() {
    return solve(identity(m,m));
  }

  /**
   * returns the square root of the matrix, i.e., X from the equation
   * X*X = A.<br/>
   * Steps in the Calculation (see <a href="http://www.mathworks.com/access/helpdesk/help/techdoc/ref/sqrtm.html" target="blank"><code>sqrtm</code></a> in Matlab):<br/>
   * <ol>
   *   <li>perform eigenvalue decomposition<br/>[V,D]=eig(A)</li>
   *   <li>take the square root of all elements in D (only the ones with 
   *       positive sign are considered for further computation)<br/>
   *       S=sqrt(D)</li>
   *   <li>calculate the root<br/>
   *       X=V*S/V, which can be also written as X=(V'\(V*S)')'</li>
   * </ol>
   * <p/>
   * <b>Note:</b> since this method uses other high-level methods, it generates
   * several instances of matrices. This can be problematic with large
   * matrices.
   * <p/>
   * Examples:
   * <ol>
   *   <li>
   *   <pre>
   *  X =
   *   5   -4    1    0    0
   *  -4    6   -4    1    0
   *   1   -4    6   -4    1
   *   0    1   -4    6   -4
   *   0    0    1   -4    5
   * 
   *  sqrt(X) =
   *   2   -1   -0   -0   -0 
   *  -1    2   -1    0   -0 
   *   0   -1    2   -1    0 
   *  -0    0   -1    2   -1 
   *  -0   -0   -0   -1    2 
   *  
   *  Matrix m = new Matrix(new double[][]{{5,-4,1,0,0},{-4,6,-4,1,0},{1,-4,6,-4,1},{0,1,-4,6,-4},{0,0,1,-4,5}});
   *   </pre>
   *   </li>
   *   <li>
   *   <pre>
   *  X =
   *   7   10
   *  15   22
   *  
   *  sqrt(X) =
   *  1.5667    1.7408
   *  2.6112    4.1779
   * 
   *  Matrix m = new Matrix(new double[][]{{7, 10},{15, 22}});
   *   </pre>
   *   </li>
   * </ol>
   *
   * @return    sqrt(A)
   */
  Matrix sqrt() {
    EigenvalueDecomposition   evd;
    Matrix                    s;
    Matrix                    v;
    Matrix                    d;
    Matrix                    result;
    Matrix                    a;
    Matrix                    b;
    int                       i;
    int                       n;

    result = null;
    
    // eigenvalue decomp.
    // [V, D] = eig(A) with A = this
    evd = this.eig();
    v   = evd.getV();
    d   = evd.getD();

    // S = sqrt of cells of D
    s = new Matrix(d.getRowDimension(), d.getColumnDimension());
    for (i = 0; i < s.getRowDimension(); i++)
      for (n = 0; n < s.getColumnDimension(); n++)
        s.set(i, n, Strictsqrt(d.get(i, n)));

    // to calculate:
    //      result = V*S/V
    //
    //    with   X = B/A
    //    and  B/A = (A'\B')'
    //    and V=A and V*S=B
    // we get 
    //      result = (V'\(V*S)')'
    //      
    //         A*X = B
    //           X = A\B
    // which is 
    //           X = A.solve(B)
    //           
    // with A=V' and B=(V*S)' 
    // we get
    //           X = V'.solve((V*S)')
    // or
    //      result = X'
    //
    // which is in full length
    //      result = (V'.solve((V*S)'))'
    a      = v.inverse();
    b      = v.times(s).inverse();
    v      = null;
    d      = null;
    evd    = null;
    s      = null;
    result = a.solve(b).inverse();

    return result;
  }

  /**
   * Performs a (ridged) linear regression.
   * (FracPete: taken from old weka.core.Matrix class)
   *
   * @param     y the dependent variable vector
   * @param     ridge the ridge parameter
   * @return    the coefficients 
   * @throws    IllegalArgumentException if not successful
   */
  LinearRegression regression(Matrix y, double ridge) {
    return new LinearRegression(this, y, ridge);
  }

  /**
   * Performs a weighted (ridged) linear regression. 
   * (FracPete: taken from old weka.core.Matrix class)
   *
   * @param     y the dependent variable vector
   * @param     w the array of data point weights
   * @param     ridge the ridge parameter
   * @return    the coefficients 
   * @throws    IllegalArgumentException if the wrong number of weights were
   *            provided.
   */
  final LinearRegression regression(Matrix y, double[] w, double ridge) {
    return new LinearRegression(this, y, w, ridge);
  }

  /** 
   * Matrix determinant
   * @return     determinant
   */
  double det() {
    return new LUDecomposition(this).det();
  }

  /** 
   * Matrix rank
   * @return     effective numerical rank, obtained from SVD.
   */
  int rank() {
    return new SingularValueDecomposition(this).rank();
  }

  /** 
   * Matrix condition (2 norm)
   * @return     ratio of largest to smallest singular value.
   */
  double cond() {
    return new SingularValueDecomposition(this).cond();
  }

  /** 
   * Matrix trace.
   * @return     sum of the diagonal elements.
   */
  double trace() {
    double t = 0;
    for (int i = 0; i < min(m,n); i++) {
      t += A[i][i];
    }
    return t;
  }

  /** 
   * Generate matrix with random elements
   * @param m    Number of rows.
   * @param n    Number of colums.
   * @return     An m-by-n matrix with uniformly distributed random elements.
   */
  static Matrix random(int m, int n) {
    Matrix A = new Matrix(m,n);
    double[][] X = A.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        X[i][j] = random();
      }
    }
    return A;
  }

  /** 
   * Generate identity matrix
   * @param m    Number of rows.
   * @param n    Number of colums.
   * @return     An m-by-n matrix with ones on the diagonal and zeros elsewhere.
   */
  static Matrix identity(int m, int n) {
    Matrix A = new Matrix(m,n);
    double[][] X = A.getArray();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        X[i][j] = (i == j ? 1.0 : 0.0);
      }
    }
    return A;
  }

  /** 
   * Print the matrix to stdout.   Line the elements up in columns
   * with a Fortran-like 'Fw.d' style format.
   * @param w    Column width.
   * @param d    Number of digits after the decimal.
   */
  void print(int w, int d) {
    print(new PrintWriter(System.out,true),w,d); 
  }

  /** 
   * Print the matrix to the output stream.   Line the elements up in
   * columns with a Fortran-like 'Fw.d' style format.
   * @param output Output stream.
   * @param w      Column width.
   * @param d      Number of digits after the decimal.
   */
  void print(PrintWriter output, int w, int d) {
    DecimalFormat format = new DecimalFormat();
    format.setDecimalFormatSymbols(new DecimalFormatSymbols(Locale.US));
    format.setMinimumIntegerDigits(1);
    format.setMaximumFractionDigits(d);
    format.setMinimumFractionDigits(d);
    format.setGroupingUsed(false);
    print(output,format,w+2);
  }

  /** 
   * Print the matrix to stdout.  Line the elements up in columns.
   * Use the format object, and right justify within columns of width
   * characters.
   * Note that is the matrix is to be read back in, you probably will want
   * to use a NumberFormat that is set to US Locale.
   * @param format A  Formatting object for individual elements.
   * @param width     Field width for each column.
   * @see java.text.DecimalFormat#setDecimalFormatSymbols
   */
  void print(NumberFormat format, int width) {
    print(new PrintWriter(System.out,true),format,width); 
  }

  // DecimalFormat is a little disappointing coming from Fortran or C's printf.
  // Since it doesn't pad on the left, the elements will come out different
  // widths.  Consequently, we'll pass the desired column width in as an
  // argument and do the extra padding ourselves.

  /** 
   * Print the matrix to the output stream.  Line the elements up in columns.
   * Use the format object, and right justify within columns of width
   * characters.
   * Note that is the matrix is to be read back in, you probably will want
   * to use a NumberFormat that is set to US Locale.
   * @param output the output stream.
   * @param format A formatting object to format the matrix elements 
   * @param width  Column width.
   * @see java.text.DecimalFormat#setDecimalFormatSymbols
   */
  void print(PrintWriter output, NumberFormat format, int width) {
    output.println();  // start on new line.
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        string s = format.format(A[i][j]); // format the number
        int padding = max(1,width-s.length()); // At _least_ 1 space
        for (int k = 0; k < padding; k++)
          output.print(' ');
        output.print(s);
      }
      output.println();
    }
    output.println();   // end with blank line.
  }

  /** 
   * Read a matrix from a stream.  The format is the same the print method,
   * so printed matrices can be read back in (provided they were printed using
   * US Locale).  Elements are separated by
   * whitespace, all the elements for each row appear on a single line,
   * the last row is followed by a blank line.
   * <p/>
   * Note: This format differs from the one that can be read via the
   * Matrix(Reader) constructor! For that format, the write(Writer) method
   * is used (from the original weka.core.Matrix class).
   *
   * @param input the input stream.
   * @see #Matrix(Reader)
   * @see #write(Writer)
   */
  static Matrix read(BufferedReader input) throws java.io.IOException {
    StreamTokenizer tokenizer= new StreamTokenizer(input);

    // Although StreamTokenizer will parse numbers, it doesn't recognize
    // scientific notation (E or D); however, Double.valueOf does.
    // The strategy here is to disable StreamTokenizer's number parsing.
    // We'll only get whitespace delimited words, EOL's and EOF's.
    // These words should all be numbers, for Double.valueOf to parse.

    tokenizer.resetSyntax();
    tokenizer.wordChars(0,255);
    tokenizer.whitespaceChars(0, ' ');
    tokenizer.eolIsSignificant(true);
    java.util.Vector v = new java.util.Vector();

    // Ignore initial empty lines
    while (tokenizer.nextToken() == StreamTokenizer.TT_EOL);
    if (tokenizer.ttype == StreamTokenizer.TT_EOF)
      throw new java.io.IOException("Unexpected EOF on matrix read.");
    do {
      v.addElement(Double.valueOf(tokenizer.sval)); // Read & store 1st row.
    } while (tokenizer.nextToken() == StreamTokenizer.TT_WORD);

    int n = v.size();  // Now we've got the number of columns!
    double row[] = new double[n];
    for (int j=0; j<n; j++)  // extract the elements of the 1st row.
      row[j]=((Double)v.elementAt(j)).doubleValue();
    v.removeAllElements();
    v.addElement(row);  // Start storing rows instead of columns.
    while (tokenizer.nextToken() == StreamTokenizer.TT_WORD) {
      // While non-empty lines
      v.addElement(row = new double[n]);
      int j = 0;
      do {
        if (j >= n) throw new java.io.IOException
          ("Row " + v.size() + " is too long.");
        row[j++] = Double.valueOf(tokenizer.sval).doubleValue();
      } while (tokenizer.nextToken() == StreamTokenizer.TT_WORD);
      if (j < n) throw new java.io.IOException
        ("Row " + v.size() + " is too short.");
    }
    int m = v.size();  // Now we've got the number of rows.
    double[][] A = new double[m][];
    v.copyInto(A);  // copy the rows out of the vector
    return new Matrix(A);
  }

  /**
   * Writes out a matrix. The format can be read via the Matrix(Reader)
   * constructor.
   * (FracPete: taken from old weka.core.Matrix class)
   *
   * @param     w the output Writer
   * @throws    Exception if an error occurs
   * @see       #Matrix(Reader)
   */
  void write(Writer w) throws Exception {
    w.write("% Rows\tColumns\n");
    w.write("" + getRowDimension() + "\t" + getColumnDimension() + "\n");
    w.write("% Matrix elements\n");
    for(int i = 0; i < getRowDimension(); i++) {
      for(int j = 0; j < getColumnDimension(); j++)
        w.write("" + get(i, j) + "\t");
      w.write("\n");
    }
    w.flush();
  }

  /** 
   * Converts a matrix to a string.
   * (FracPete: taken from old weka.core.Matrix class)
   *
   * @return    the converted string
   */
  string toString() {
    // Determine the width required for the maximum element,
    // and check for fractional display requirement.
    double maxval = 0;
    boolean fractional = false;
    for (int i = 0; i < getRowDimension(); i++) {
      for (int j = 0; j < getColumnDimension(); j++) {
        double current = get(i, j);
        if (current < 0)
          current *= -11;
        if (current > maxval)
          maxval = current;
        double fract = abs(current - rint(current));
        if (!fractional
            && ((log(fract) / log(10)) >= -2)) {
          fractional = true;
        }
      }
    }
    int width = (int)(log(maxval) / log(10) 
        + (fractional ? 4 : 1));

    StringBuffer text = new StringBuffer();   
    for (int i = 0; i < getRowDimension(); i++) {
      for (int j = 0; j < getColumnDimension(); j++)
        text.append(" ").append(Utils.doubleToString(get(i, j),
              width, (fractional ? 2 : 0)));
      text.append("\n");
    }

    return text.toString();
  } 

  /**
   * converts the Matrix into a single line Matlab string: matrix is enclosed 
   * by parentheses, rows are separated by semicolon and single cells by
   * blanks, e.g., [1 2; 3 4].
   * @return      the matrix in Matlab single line format
   */
  string toMatlab() {
    StringBuffer      result;
    int               i;
    int               n;

    result = new StringBuffer();

    result.append("[");

    for (i = 0; i < getRowDimension(); i++) {
      if (i > 0)
        result.append("; ");
      
      for (n = 0; n < getColumnDimension(); n++) {
        if (n > 0)
          result.append(" ");
        result.append(Double.toString(get(i, n)));
      }
    }
    
    result.append("]");

    return result.toString();
  }

  /**
   * creates a matrix from the given Matlab string.
   * @param matlab  the matrix in matlab format
   * @return        the matrix represented by the given string
   * @see           #toMatlab()
   */
  static Matrix parseMatlab(string matlab) throws Exception {
    StringTokenizer   tokRow;
    StringTokenizer   tokCol;
    int               rows;
    int               cols;
    Matrix            result;
    string            cells;
    
    // get content
    cells = matlab.substring(
              matlab.indexOf("[") + 1, matlab.indexOf("]")).trim();
    
    // determine dimenions
    tokRow = new StringTokenizer(cells, ";");
    rows   = tokRow.countTokens();
    tokCol = new StringTokenizer(tokRow.nextToken(), " ");
    cols   = tokCol.countTokens();
    
    // fill matrix
    result = new Matrix(rows, cols);
    tokRow = new StringTokenizer(cells, ";");
    rows   = 0;
    while (tokRow.hasMoreTokens()) {
      tokCol = new StringTokenizer(tokRow.nextToken(), " ");
      cols   = 0;
      while (tokCol.hasMoreTokens()) {
        result.set(rows, cols, Double.parseDouble(tokCol.nextToken()));
        cols++;
      }
      rows++;
    }
    
    return result;
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.8 $");
  }
  
  /**
   * Main method for testing this class.
   */
  static void main(string[] args) {
    Matrix        I;
    Matrix        A;
    Matrix        B;

    try {
      // Identity
      cout << "\nIdentity\n" << endl;
      I = Matrix.identity(3, 5);
      cout << "I(3,5)\n" << I << endl;
      
      // basic operations - square
      cout << "\nbasic operations - square\n");
      A = Matrix.random(3, 3);
      B = Matrix.random(3, 3);
      cout << "A\n" << A << endl;
      cout << "B\n" << B << endl;
      cout << "A'\n" << A.inverse() << endl;
      cout << "A^T\n" << A.transpose() << endl;
      cout << "A+B\n" << A.plus(B) << endl;
      cout << "A*B\n" << A.times(B) << endl;
      cout << "X from A*X=B\n" << A.solve(B) << endl;

      // basic operations - non square
      cout << "\nbasic operations - non square\n" << endl;
      A = Matrix.random(2, 3);
      B = Matrix.random(3, 4);
      cout << "A\n" << A << endl;
      cout << "B\n" << B << endl;
      cout << "A*B\n" << A.times(B) << endl;

      // sqrt
      cout << "\nsqrt (1)\n" << endl;
      A = new Matrix(new double[][]{{5,-4,1,0,0},{-4,6,-4,1,0},{1,-4,6,-4,1},{0,1,-4,6,-4},{0,0,1,-4,5}});
      cout << "A\n" << A << endl;
      cout << "sqrt(A)\n" << A.sqrt() << endl;

      // sqrt
      cout << "\nsqrt (2)\n" << endl;
      A = new Matrix(new double[][]{{7, 10},{15, 22}});
      cout << "A\n" << A << endl;
      cout << "sqrt(A)\n" << A.sqrt() << endl;
      cout << "det(A)\n" << A.det() << "\n" << endl;

      // eigenvalue decomp.
      cout << "\nEigenvalue Decomposition\n" << endl;
      EigenvalueDecomposition evd = A.eig();
      cout << "[V,D] = eig(A)" << endl;
      cout << "- V\n" << evd.getV() << endl;
      cout << "- D\n" << evd.getD() << endl;

      // LU decomp.
      cout << "\nLU Decomposition\n" << endl;
      LUDecomposition lud = A.lu();
      cout << "[L,U,P] = lu(A)" << endl;
      cout << "- L\n" << lud.getL() << endl;
      cout << "- U\n" << lud.getU() << endl;
      cout << "- P\n" << Utils.arrayToString(lud.getPivot()) << "\n" << endl;

      // regression
      cout << "\nRegression\n" << endl;
      B = new Matrix(new double[][]{{3},{2}});
      double ridge = 0.5;
      double[] weights = new double[]{0.3, 0.7};
      LinearRegression lr = A.regression(B, ridge);
      cout << "A\n" << A << endl;
      cout << "B\n" << B << endl;
      cout << "ridge = " << ridge << "\n" << endl;
      cout << "weights = " << Utils.arrayToString(weights) << "\n" << endl;
      cout << "A.regression(B, ridge)\n" 
          << A.regression(B, ridge) << "\n" << endl;
      cout << "A.regression(B, weights, ridge)\n" 
          << A.regression(B, weights, ridge) << "\n" << endl;

      // writer/reader
      cout << "\nWriter/Reader\n" << endl;
      StringWriter writer = new StringWriter();
      A.write(writer);
      cout << "A.write(Writer)\n" << writer << endl;
      A = new Matrix(new StringReader(writer.toString()));
      cout << "A = new Matrix.read(Reader)\n" << A << endl;

      // Matlab
      cout << "\nMatlab-Format\n" << endl;
      string matlab = "[ 1   2;3 4 ]";
      cout << "Matlab: " << matlab << endl;
      cout << "from Matlab:\n" << Matrix.parseMatlab(matlab) << endl;
      cout << "to Matlab:\n" << Matrix.parseMatlab(matlab).toMatlab() << endl;
      matlab = "[1 2 3 4;3 4 5 6;7 8 9 10]";
      cout << "Matlab: " << matlab << endl;
      cout << "from Matlab:\n" << Matrix.parseMatlab(matlab) << endl;
cout << "to Matlab:\n" << Matrix.parseMatlab(matlab).toMatlab() << "\n" << endl;
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}
