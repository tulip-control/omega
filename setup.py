"""Installation script."""
import setuptools
# inline:
# from omega.logic import lexyacc
# import git


PACKAGE_NAME = 'omega'
DESCRIPTION = (
    'Symbolic algorithms for solving '
    'games of infinite duration.')
PACKAGE_URL = f'https://github.com/tulip-control/{PACKAGE_NAME}'
PROJECT_URLS = {
    'Bug Tracker':
        'https://github.com/tulip-control/omega/issues',
    'Documentation':
        'https://github.com/tulip-control/omega/blob/main/doc/doc.md',
    'Source Code':
        'https://github.com/tulip-control/omega'}
README = 'README.md'
VERSION_FILE = f'{PACKAGE_NAME}/_version.py'
MAJOR = 0
MINOR = 4
MICRO = 0
VERSION = f'{MAJOR}.{MINOR}.{MICRO}'
VERSION_FILE_TEXT = (
    '# This file was generated from setup.py\n'
    "version = '{version}'\n")
PYTHON_REQUIRES = '>=3.11'
INSTALL_REQUIRES = [
    'astutils >= 0.0.5',
    'dd >= 0.6.0',
    'natsort >= 3.5.3',
    'networkx >= 2.0',
    'ply >= 3.6, <= 3.10',
    'pydot >= 1.2.2']
TESTS_REQUIRE = ['pytest >= 4.6.11']
CLASSIFIERS = [
    'Development Status :: 2 - Pre-Alpha',
    'Intended Audience :: Science/Research',
    'License :: OSI Approved :: BSD License',
    'Operating System :: OS Independent',
    'Programming Language :: Python',
    'Programming Language :: Python :: 3 :: Only',
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
    latest_version = _parse_version(latest_tag[1:])
    given_version = _parse_version(version)
    if latest_version > given_version:
        raise AssertionError(
            (latest_tag, version))
    sha = repo.head.commit.hexsha
    if repo.is_dirty():
        return f'{version}.dev0+{sha}.dirty'
    # commit is clean
    # is it release of `version` ?
    try:
        tag = repo.git.describe(
            match='v[0-9]*', exact_match=True,
            tags=True, dirty=True)
    except git.GitCommandError:
        return f'{version}.dev0+{sha}'
    assert tag == 'v' + version, (tag, version)
    return version


def _parse_version(
        version:
            str
        ) -> tuple[
            int, int, int]:
    """Return numeric version."""
    numerals = version.split('.')
    if len(numerals) != 3:
        raise ValueError(numerals)
    return tuple(map(int, numerals))


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
    _build_parser()
    with open(README) as fd:
        long_description = fd.read()
    setuptools.setup(
        name=PACKAGE_NAME,
        version=version,
        description=DESCRIPTION,
        long_description=long_description,
        long_description_content_type='text/markdown',
        author='Caltech Control and Dynamical Systems',
        author_email='tulip@tulip-control.org',
        url=PACKAGE_URL,
        project_urls=PROJECT_URLS,
        license='BSD',
        python_requires=PYTHON_REQUIRES,
        install_requires=INSTALL_REQUIRES,
        tests_require=TESTS_REQUIRE,
        packages=[
            PACKAGE_NAME,
            'omega.games',
            'omega.logic',
            'omega.symbolic'],
        package_dir={PACKAGE_NAME: PACKAGE_NAME},
        classifiers=CLASSIFIERS,
        keywords=KEYWORDS)


def _build_parser():
    """Cache the parser's LALR(1) state machine."""
    try:
        import astutils
        import ply
    except ImportError:
        print(
            'WARNING: `omega` could not cache '
            'parser tables (this message can '
            'be ignored if running only for '
            '"egg_info").')
        return
    from omega.logic import lexyacc
    lexyacc._rewrite_tables(
        outputdir='./omega/logic/')


if __name__ == '__main__':
    run_setup()
