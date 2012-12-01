/*
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License as published by
 *    the Free Software Foundation; either version 2 of the License, or (at
 *    your option) any later version.
 *
 *    This program is distributed in the hope that it will be useful, but
 *    WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *    General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.  */

/*
 *    FlexibleDecimalFormat.cpp
 *    Copyright (C) 2002 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core.matrix;

// import weka.core.RevisionHandler;
// import weka.core.RevisionUtils;

// import java.text.DecimalFormat;
// import java.text.FieldPosition;

/**
 * @author Shumin Guo
 * @version $Revision: 1.4 $
 */
class FlexibleDecimalFormat : public DecimalFormat, public RevisionHandler {
private:
  /** for serialization */
  static final long serialVersionUID = 110912192794064140L;

  DecimalFormat nf = null;
  int      digits = 7;
  bool  exp = false; 
  int      intDigits = 1;
  int      decimalDigits = 0;
  int      expIntDigits = 1;          // ??? 
  int      expDecimalDigits = 0;      // ???
  int      power = 2;
  bool  trailing = false;
  bool  grouping = false;
  bool  sign = false;
    
public: 
  FlexibleDecimalFormat ( ) {
    this( 5 );
  }

  FlexibleDecimalFormat ( int digits ) {
    if( digits < 1 ) 
      throw new IllegalArgumentException("digits < 1");
    this.digits = digits;
    intDigits = 1;
  }

  FlexibleDecimalFormat ( int digits, bool trailing ) {
    this( digits );
    this.trailing = trailing;
  }

  FlexibleDecimalFormat ( int digits, bool exp, bool trailing, 
				 bool grouping ) {
    this.trailing = trailing;
    this.exp = exp;
    this.digits = digits;
    this.grouping = grouping;
    if( exp ) {
      this.intDigits = 1;
      this.decimalDigits = digits - intDigits;
    }
    else {
      this.decimalDigits = decimalDigits;
      this.intDigits = Math.max( 1, digits - decimalDigits );
    }
  }

  FlexibleDecimalFormat ( double d ) {
    newFormat( d );
  }

private: 
  void newFormat ( double d ) {
    if( needExponentialFormat( d ) ) {
      exp = true;
      intDigits = 1;
      expDecimalDigits = decimalDigits( d, true );
      if( d < 0) sign = true;
      else sign = false;
    }
    else {
      exp = false;
      intDigits = Math.max(1, intDigits( d ));
      decimalDigits = decimalDigits( d, false );
      if( d < 0.0 ) sign = true;
      else sign = false;
    }
  }

  static void println ( Object obj ){
    cout << obj << endl;
  }

  void setFormat ( ) {
    int dot = 1;
    if( decimalDigits == 0) dot = 0;
    if( exp ) 
      nf = new ExponentialFormat( 1 + expDecimalDigits, power, sign, 
				  grouping || trailing );
    else { 
      int s = sign ? 1 : 0;
      nf = new FloatingPointFormat( s +intDigits +dot +decimalDigits, 
				    decimalDigits, grouping || trailing);
    }
  }
    
  void setFormat ( double d ) {
    newFormat( d );
    setFormat();
  }

  int decimalDigits ( double d, bool expo ) {
    if( d == 0.0 ) return 0;
    d = Math.abs( d );
    int e = intDigits( d );
    if( expo ) {
      d /= Math.pow(10, e-1);
      e = 1;
    }
    if( e >= digits ) return 0;
    int iD = Math.max(1, e);  
    int dD = digits - e;
    if( !trailing && dD > 0 ) {  // to get rid of trailing zeros
      FloatingPointFormat f = new 
	FloatingPointFormat( iD + 1 + dD, dD, true);
      string dString = f.format( d );
      while( dD > 0 ) {
	if( dString.charAt(iD+1+dD-1) == '0' ) {
	  dD--;
	}
	else break;
      }
    }
    return dD;
  }

  static int intDigits ( double d ) {
    return (int) Math.floor( Math.log( Math.abs( d * (1 + 1e-14) ) ) / 
			     Math.log ( 10 ) ) + 1;
  }

public: 
  void update ( double d ) {
    if( Math.abs( intDigits(d) -1 ) > 99 ) power = 3;
    expIntDigits = 1;
    expDecimalDigits = Math.max( expDecimalDigits, 
				 decimalDigits( d, true ));
    if( d < 0) sign = true;
    if( needExponentialFormat( d ) || exp ) {
      exp = true;
    }
    else {
      intDigits = Math.max(intDigits, intDigits( d ));
      decimalDigits = Math.max(decimalDigits, decimalDigits( d, false ));
      if( d < 0) sign = true;
    }
  }
        
  bool  needExponentialFormat ( double d ) {
    if( d == 0.0 ) return false;
    int e = intDigits( d );
    if( e > digits + 5 || e < -3 ) return true;
    else return false;
  }
    
  void grouping ( bool grouping ) {
    this.grouping = grouping;
  }
    
  StringBuffer format (double number, StringBuffer toAppendTo,
			      FieldPosition pos) {
    if( grouping ) {
      if( nf == null ) {
	setFormat();
      }
    }
    else setFormat( number );
	
    return toAppendTo.append( nf.format(number) );
  }

  int width () {
	
    if( !trailing && !grouping ) 
      throw new RuntimeException( "flexible width" );
	
    return format(0.).length();
  }
    
  StringBuffer formatString ( string str ) {
    int w = width();
    int h = ( w - str.length() ) / 2;
    StringBuffer text = new StringBuffer();
    for(int i = 0; i < h; i++ ){
      text.append( ' ' );
    }
    text.append( str );
    for(int i = 0; i < w - h - str.length(); i++ ){
      text.append( ' ' );
    }
    return text;
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.4 $");
  }
}


