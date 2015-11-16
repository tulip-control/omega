from setuptools import setup
# inline:
# from omega.logic import lexyacc


name = 'omega'
description = 'Algorithms related to omega regular languages.'
url = 'https://github.com/johnyf/{name}'.format(name=name)
README = 'README.md'
VERSION_FILE = '{name}/_version.py'.format(name=name)
MAJOR = 0
MINOR = 0
MICRO = 4
version = '{major}.{minor}.{micro}'.format(
    major=MAJOR, minor=MINOR, micro=MICRO)
s = (
    '# This file was generated from setup.py\n'
    "version = '{version}'\n").format(version=version)
install_requires = [
    'dd >= 0.2.0',
    'ply >= 3.6',
    'natsort >= 3.5.3',
    'networkx >= 1.9.1']
tests_require = ['nose >= 1.3.4']
classifiers = [
    'Development Status :: 2 - Pre-Alpha',
    'Intended Audience :: Science/Research',
    'License :: OSI Approved :: BSD License',
    'Operating System :: OS Independent',
    'Programming Language :: Python',
    'Programming Language :: Python :: 2',
    'Programming Language :: Python :: 2.7',
    'Topic :: Scientific/Engineering']


if __name__ == '__main__':
    with open(VERSION_FILE, 'w') as f:
        f.write(s)
    try:
        from omega.logic import lexyacc
        lexyacc._rewrite_tables(outputdir='./omega/logic/')
    except ImportError:
        print('WARNING: `omega` could not cache parser tables '
              '(ignore this if running only for "egg_info").')
    setup(
        name=name,
        version=version,
        description=description,
        long_description=open(README).read(),
        author='Ioannis Filippidis',
        author_email='jfilippidis@gmail.com',
        url=url,
        license='BSD',
        install_requires=install_requires,
        tests_require=tests_require,
        packages=[name, 'omega.games', 'omega.logic', 'omega.symbolic'],
        package_dir={name: name},
        classifiers=classifiers,
        keywords=['logic'])
