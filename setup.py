"""Installation script."""
from setuptools import setup
from pkg_resources import parse_version
# inline:
# from omega.logic import lexyacc
# import git


PACKAGE_NAME = 'omega'
DESCRIPTION = (
    'Symbolic algorithms for solving '
    'games of infinite duration.')
PACKAGE_URL = 'https://github.com/tulip-control/{name}'.format(name=PACKAGE_NAME)
README = 'README.md'
VERSION_FILE = '{name}/_version.py'.format(name=PACKAGE_NAME)
MAJOR = 0
MINOR = 4
MICRO = 0
VERSION = '{major}.{minor}.{micro}'.format(
    major=MAJOR, minor=MINOR, micro=MICRO)
VERSION_FILE_TEXT = (
    '# This file was generated from setup.py\n'
    "version = '{version}'\n")
INSTALL_REQUIRES = [
    'astutils >= 0.0.3',
    'dd >= 0.5.5',
    'humanize >= 0.5.1',
    'natsort >= 3.5.3',
    'networkx >= 2.0',
    'ply >= 3.6, <= 3.10',
    'pydot >= 1.2.2']
SETUP_REQUIRES = ['setuptools >= 38.6.0']
TESTS_REQUIRE = ['nose >= 1.3.4']
CLASSIFIERS = [
    'Development Status :: 2 - Pre-Alpha',
    'Intended Audience :: Science/Research',
    'License :: OSI Approved :: BSD License',
    'Operating System :: OS Independent',
    'Programming Language :: Python',
    'Programming Language :: Python :: 2.7',
    'Programming Language :: Python :: 3',
    'Programming Language :: Python :: 3.4',
    'Programming Language :: Python :: 3.5',
    'Programming Language :: Python :: 3.6',
    'Programming Language :: Python :: 3.7',
    'Programming Language :: Python :: 3.8',
    'Programming Language :: Python :: 3.9',
    'Topic :: Scientific/Engineering']
KEYWORDS = [
    'first-order', 'propositional', 'logic',
    'quantifier', 'forall', 'exists',
    'fixpoint', 'mu-calculus', 'formula', 'flatten',
    'bitblaster', 'bitvector', 'arithmetic',
    'binary decision diagram', 'symbolic',
    'games', 'specification', 'system',
    'assume', 'guarantee', 'satisfiability',
    'enumeration', 'state machine',
    'transition system', 'automaton', 'automata',
    'streett', 'rabin',
    'temporal logic', 'temporal tester',
    'gr1', 'generalized reactivity']


def git_version(version):
    """Return version with local version identifier."""
    import git
    repo = git.Repo('.git')
    repo.git.status()
    # assert versions are increasing
    latest_tag = repo.git.describe(
        match='v[0-9]*', tags=True, abbrev=0)
    assert parse_version(latest_tag) <= parse_version(version), (
        latest_tag, version)
    sha = repo.head.commit.hexsha
    if repo.is_dirty():
        return '{v}.dev0+{sha}.dirty'.format(
            v=version, sha=sha)
    # commit is clean
    # is it release of `version` ?
    try:
        tag = repo.git.describe(
            match='v[0-9]*', exact_match=True,
            tags=True, dirty=True)
    except git.GitCommandError:
        return '{v}.dev0+{sha}'.format(
            v=version, sha=sha)
    assert tag == 'v' + version, (tag, version)
    return version


def run_setup():
    """Build parser, get version from `git`, install."""
    # version
    try:
        version = git_version(VERSION)
    except:
        print('No git info: Assume release.')
        version = VERSION
    s = VERSION_FILE_TEXT.format(version=version)
    with open(VERSION_FILE, 'w') as f:
        f.write(s)
    # build parser
    try:
        from omega.logic import lexyacc
        lexyacc._rewrite_tables(outputdir='./omega/logic/')
    except ImportError:
        print('WARNING: `omega` could not cache parser tables '
              '(ignore this if running only for "egg_info").')
    with open(README) as fd:
        long_description = fd.read()
    setup(
        name=PACKAGE_NAME,
        version=version,
        description=DESCRIPTION,
        long_description=long_description,
        long_description_content_type='text/markdown',
        author='Caltech Control and Dynamical Systems',
        author_email='tulip@tulip-control.org',
        url=PACKAGE_URL,
        license='BSD',
        setup_requires=SETUP_REQUIRES,
        install_requires=INSTALL_REQUIRES,
        tests_require=TESTS_REQUIRE,
        packages=[PACKAGE_NAME, 'omega.games',
                  'omega.logic', 'omega.symbolic'],
        package_dir={PACKAGE_NAME: PACKAGE_NAME},
        classifiers=CLASSIFIERS,
        keywords=KEYWORDS)


if __name__ == '__main__':
    run_setup()
