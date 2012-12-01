#include "Random.hpp"

using namespace std; 

int Random::nextInt() {
  return ceil(rand());
}

float Random::nextFloat() {
  return (float)rand(); 
}


double Random::nextDouble() {
  return rand(); 
}
