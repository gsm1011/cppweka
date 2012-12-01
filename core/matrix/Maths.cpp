/*
 * This software is a cooperative product of The MathWorks and the National
 * Institute of Standards and Technology (NIST) which has been released to the
 * public domain. Neither The MathWorks nor NIST assumes any responsibility
 * whatsoever for its use by other parties, and makes no guarantees, expressed
 * or implied, about its quality, reliability, or any other characteristic.
 */

/*
 * Maths.cpp
 * Copyright (C) 1999 The Mathworks and NIST
 *
 */

// package weka.core.matrix;

// import weka.core.RevisionHandler;
// import weka.core.RevisionUtils;
// import weka.core.Statistics;

// import java.util.Random;

/**
 * Utility class.
 * <p/>
 * Adapted from the <a href="http://math.nist.gov/javanumerics/jama/" target="_blank">JAMA</a> package.
 *
 * @author Shumin Guo
 * @author Shumin Guo @ wright state university. 
 * @version $Revision: 1.3 $
 */
#inclue <stdio.h> 
#include <iostream>
#include <cmath> 

using namespace std; 

class Maths : public RevisionHandler {
public: 
  /** The constant 1 / sqrt(2 pi) */
  const static double PSI = 0.3989422804014327028632;

  /** The constant - log( sqrt(2 pi) ) */
  const static double logPSI = -0.9189385332046726695410;

  /** Distribution type: undefined */
  const static int undefinedDistribution = 0;

  /** Distribution type: noraml */
  const static int normalDistribution = 1;

  /** Distribution type: chi-squared */
  const static int chisqDistribution = 2;

  /** 
   * sqrt(a^2 + b^2) without under/overflow. 
   */
  static double hypot(double a, double b) {
    double r;
    if (abs(a) > abs(b)) {
      r = b/a;
      r = abs(a)*sqrt(1+r*r);
    } else if (b != 0) {
      r = a/b;
      r = abs(b)*sqrt(1+r*r);
    } else {
      r = 0.0;
    }
    return r;
  }

  /**
   *  Returns the square of a value
   *  @param x 
   *  @return the square
   */
  static double  square( double x ) {
    return x * x;
  }

  /* methods for normal distribution */

  /**
   *  Returns the cumulative probability of the standard normal.
   *  @param x the quantile
   */
  static double  pnorm( double x ) {
    return Statistics.normalProbability( x );
  }
    
  /** 
   *  Returns the cumulative probability of a normal distribution.
   *  @param x the quantile
   *  @param mean the mean of the normal distribution
   *  @param sd the standard deviation of the normal distribution.
   */
  static double  pnorm( double x, double mean, double sd ) {
    if( sd <= 0.0 )
      throw new IllegalArgumentException("standard deviation <= 0.0");
    return pnorm( (x - mean) / sd );
  }
    
  /** 
   *  Returns the cumulative probability of a set of normal distributions
   *  with different means.
   *  @param x the vector of quantiles
   *  @param mean the means of the normal distributions
   *  @param sd the standard deviation of the normal distribution.
   *  @return the cumulative probability */
  static DoubleVector  pnorm( double x, DoubleVector mean, double sd ) {
    DoubleVector p = new DoubleVector( mean.size() );
        
    for( int i = 0; i < mean.size(); i++ ) {
      p.set( i, pnorm(x, mean.get(i), sd) );
    }
    return p;
  }
    
  /** Returns the density of the standard normal.
   *  @param x the quantile
   *  @return the density
   */
  static double dnorm( double x ) {
    return exp( - x * x / 2. ) * PSI;
  }
    
  /** Returns the density value of a standard normal.
   *  @param x the quantile
   *  @param mean the mean of the normal distribution
   *  @param sd the standard deviation of the normal distribution.
   *  @return the density */
  static double dnorm( double x, double mean, double sd ) {
    if( sd <= 0.0 )
      throw new IllegalArgumentException("standard deviation <= 0.0");
    return dnorm( (x - mean) / sd );
  }
    
  /** Returns the density values of a set of normal distributions with
   *  different means.
   *  @param x the quantile
   *  @param mean the means of the normal distributions
   *  @param sd the standard deviation of the normal distribution.
   * @return the density */
  static DoubleVector dnorm( double x, DoubleVector mean, double sd ) {
    DoubleVector den = new DoubleVector( mean.size() );
        
    for( int i = 0; i < mean.size(); i++ ) {
      den.set( i, dnorm(x, mean.get(i), sd) );
    }
    return den;
  }
    
  /** Returns the log-density of the standard normal.
   *  @param x the quantile
   *  @return the density
   */
  static double dnormLog( double x ) {
    return logPSI - x * x / 2.;
  }
    
  /** Returns the log-density value of a standard normal.
   *  @param x the quantile
   *  @param mean the mean of the normal distribution
   *  @param sd the standard deviation of the normal distribution.
   *  @return the density */
  static double dnormLog( double x, double mean, double sd ) {
    if( sd <= 0.0 )
      throw new IllegalArgumentException("standard deviation <= 0.0");
    return - log(sd) + dnormLog( (x - mean) / sd );
  }
    
  /** Returns the log-density values of a set of normal distributions with
   *  different means.
   *  @param x the quantile
   *  @param mean the means of the normal distributions
   *  @param sd the standard deviation of the normal distribution.
   * @return the density */
  static DoubleVector dnormLog( double x, DoubleVector mean, double sd ) {
    DoubleVector denLog = new DoubleVector( mean.size() );
        
    for( int i = 0; i < mean.size(); i++ ) {
      denLog.set( i, dnormLog(x, mean.get(i), sd) );
    }
    return denLog;
  }
    
  /** 
   *  Generates a sample of a normal distribution.
   *  @param n the size of the sample
   *  @param mean the mean of the normal distribution
   *  @param sd the standard deviation of the normal distribution.
   *  @param random the random stream
   *  @return the sample
   */
  static DoubleVector rnorm( int n, double mean, double sd, Random random ) {
    if( sd < 0.0)
      throw new IllegalArgumentException("standard deviation < 0.0");
        
    if( sd == 0.0 ) return new DoubleVector( n, mean );
    DoubleVector v = new DoubleVector( n );
    for( int i = 0; i < n; i++ ) 
      v.set( i, (random.nextGaussian() + mean) / sd );
    return v;
  }
    
  /* methods for Chi-square distribution */

  /** Returns the cumulative probability of the Chi-squared distribution
   *  @param x the quantile
   */
  static double pchisq( double x ) {
    double xh = sqrt( x );
    return pnorm( xh ) - pnorm( -xh );
  }
    
  /** Returns the cumulative probability of the noncentral Chi-squared
   *  distribution.
   *  @param x the quantile
   *  @param ncp the noncentral parameter */
  static double pchisq( double x, double ncp ) {
    double mean = sqrt( ncp );
    double xh = sqrt( x );
    return pnorm( xh - mean ) - pnorm( -xh - mean );
  }
    
  /** Returns the cumulative probability of a set of noncentral Chi-squared
   *  distributions.
   *  @param x the quantile
   *  @param ncp the noncentral parameters */
  static DoubleVector pchisq( double x, DoubleVector ncp ) {
    int n = ncp.size();
    DoubleVector p = new DoubleVector( n );
    double mean;
    double xh = sqrt( x );
        
    for( int i = 0; i < n; i++ ) {
      mean = sqrt( ncp.get(i) );
      p.set( i, pnorm( xh - mean ) - pnorm( -xh - mean ) );
    }
    return p;
  }
    
  /** Returns the density of the Chi-squared distribution.
   *  @param x the quantile
   *  @return the density
   */
  static double dchisq( double x ) {
    if( x == 0.0 ) return Double.POSITIVE_INFINITY;
    double xh = sqrt( x );
    return dnorm( xh ) / xh;
  }
    
  /** Returns the density of the noncentral Chi-squared distribution.
   *  @param x the quantile
   *  @param ncp the noncentral parameter
   */
  static double dchisq( double x, double ncp ) {
    if( ncp == 0.0 ) return dchisq( x );
    double xh = sqrt( x );
    double mean = sqrt( ncp );
    return (dnorm( xh - mean ) + dnorm( -xh - mean)) / (2 * xh);
  }
    
  /** Returns the density of the noncentral Chi-squared distribution.
   *  @param x the quantile
   *  @param ncp the noncentral parameters 
   */
  static DoubleVector dchisq( double x, DoubleVector ncp ) {
    int n = ncp.size();
    DoubleVector d = new DoubleVector( n );
    double xh = sqrt( x );
    double mean;
    for( int i = 0; i < n; i++ ) {
      mean = sqrt( ncp.get(i) );
      if( ncp.get(i) == 0.0 ) d.set( i, dchisq( x ) );
      else d.set( i, (dnorm( xh - mean ) + dnorm( -xh - mean)) / 
                  (2 * xh) );
    }
    return d;
  }
    
  /** Returns the log-density of the noncentral Chi-square distribution.
   *  @param x the quantile
   *  @return the density
   */
  static double dchisqLog( double x ) {
    if( x == 0.0) return Double.POSITIVE_INFINITY;
    double xh = sqrt( x );
    return dnormLog( xh ) - log( xh );
  }
    
  /** Returns the log-density value of a noncentral Chi-square distribution.
   *  @param x the quantile
   *  @param ncp the noncentral parameter
   *  @return the density */
  static double dchisqLog( double x, double ncp ) {
    if( ncp == 0.0 ) return dchisqLog( x );
    double xh = sqrt( x );
    double mean = sqrt( ncp );
    return log( dnorm( xh - mean ) + dnorm( -xh - mean) ) - 
    log(2 * xh);
  }
    
  /** Returns the log-density of a set of noncentral Chi-squared
   *  distributions.
   *  @param x the quantile
   *  @param ncp the noncentral parameters */
  static DoubleVector dchisqLog( double x, DoubleVector ncp ) {
    DoubleVector dLog = new DoubleVector( ncp.size() );
    double xh = sqrt( x );
    double mean;
        
    for( int i = 0; i < ncp.size(); i++ ) {
      mean = sqrt( ncp.get(i) );
      if( ncp.get(i) == 0.0 ) dLog.set( i, dchisqLog( x ) );
      else dLog.set( i, log( dnorm( xh - mean ) + dnorm( -xh - mean) ) - 
                     log(2 * xh) );
    }
    return dLog;
  }
    
  /** 
   *  Generates a sample of a Chi-square distribution.
   *  @param n the size of the sample
   *  @param ncp the noncentral parameter
   *  @param random the random stream
   *  @return the sample
   */
  static DoubleVector rchisq( int n, double ncp, Random random ) {
    DoubleVector v = new DoubleVector( n );
    double mean = sqrt( ncp );
    double x;
    for( int i = 0; i < n; i++ ) {
      x = random.nextGaussian() + mean;
      v.set( i, x * x );
    }
    return v;
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  String getRevision() {
    return RevisionUtils.extract("$Revision: 1.3 $");
  }
}; 
