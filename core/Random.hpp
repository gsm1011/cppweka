#ifndef _WEKA_FASTVECTOR_H_
#define  _WEKA_FASTVECTOR_H_
#include <iostream>
#include <string>
#include <vector>

using namespace std; 

class Random {
public: 
  int nextInt(); 
  float nextFloat(); 
  double nextDouble(); 
  string toString() { return "random"; }
};

#endif
