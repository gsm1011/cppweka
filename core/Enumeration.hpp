#ifndef _WEKA_ENUMERATION_H_
#define  _WEKA_ENUMERATION_H_
#include "Object.hpp"

class Enumeration {
public:
  virtual bool hasMoreElements() = 0;
  virtual Object nextElement() = 0;
};

#endif
