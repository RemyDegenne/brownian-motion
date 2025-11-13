set -x -e

lake build
rm -rf html _out
lake exe manual
mkdir html
mv _out/html-multi/* html/
rm -rf _out
mkdir -p html/static
cp static_files/* html/static

cd ..
mkdir -p home_page/verso
cp -r verso/html/* home_page/verso
