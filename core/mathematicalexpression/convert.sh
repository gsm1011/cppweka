for file in *.java; do mv $file `basename $file .java`.cpp; done
sed -i 's/^import/\/\/ import/g' *.cpp
sed -i 's/^package/\/\/ package/g' *.cpp
sed -i 's/boolean/bool/g' *.cpp
sed -i 's/String /string /g' *.cpp
sed -i 's/NULL/NULL/g' *
