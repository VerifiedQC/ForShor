"""Focused build-wrapper CLI checks; all compiler processes are mocked."""
import os
from pathlib import Path
import runpy
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]


class CommandCaptured(Exception):
    pass


class BuildCliTests(unittest.TestCase):
    def compiler_command(self,arguments=(),environment_fc='',path_compiler=None):
        commands=[]
        def capture(command,**kwargs):
            commands.append((command,kwargs))
            raise CommandCaptured()
        with patch.dict(os.environ,{'FC':environment_fc}), \
             patch.object(sys,'argv',['build.py',*arguments]), \
             patch('shutil.which',side_effect=lambda name: path_compiler if name=='gfortran' else None), \
             patch('subprocess.run',side_effect=capture),patch.object(Path,'mkdir'):
            with self.assertRaises(CommandCaptured):
                runpy.run_path(str(ROOT/'build.py'),run_name='__main__')
        self.assertEqual(len(commands),1)
        command,kwargs=commands[0]
        self.assertIn('-O3',command)
        self.assertTrue(kwargs['check'])
        self.assertEqual(kwargs['cwd'],ROOT/'build'/'release')
        self.assertEqual(kwargs['env']['PATH'].split(os.pathsep)[0],str(Path(command[0]).parent))
        return command

    def test_argument_bare_compiler_uses_path_and_overrides_fc(self):
        compiler=ROOT/'synthetic-path-bin'/'gfortran.exe'
        command=self.compiler_command(['--compiler','gfortran'],
                                      environment_fc='different-compiler',path_compiler=str(compiler))
        self.assertEqual(command[0],str(compiler.resolve()))

    def test_environment_bare_compiler_uses_path(self):
        compiler=ROOT/'synthetic-path-bin'/'gfortran.exe'
        command=self.compiler_command(environment_fc='gfortran',path_compiler=str(compiler))
        self.assertEqual(command[0],str(compiler.resolve()))

    def test_explicit_paths_are_preserved(self):
        for compiler in [str(ROOT/'explicit-bin'/'gfortran.exe'),
                         './relative-bin/gfortran.exe','./gfortran.exe']:
            for option in ['argument','environment']:
                with self.subTest(compiler=compiler,option=option):
                    command=self.compiler_command(
                        ['--compiler',compiler] if option=='argument' else [],
                        environment_fc=compiler if option=='environment' else '',
                        path_compiler=str(ROOT/'wrong-path-bin'/'gfortran.exe'))
                    self.assertEqual(command[0],str(Path(compiler).resolve()))

    def test_implicit_path_discovery_is_preserved(self):
        compiler=ROOT/'synthetic-path-bin'/'gfortran.exe'
        self.assertEqual(self.compiler_command(path_compiler=str(compiler))[0],str(compiler.resolve()))

    def test_missing_explicit_name_does_not_fall_back(self):
        for option in ['argument','environment']:
            with self.subTest(option=option),patch.dict(os.environ,{
                    'FC':'missing-fortran' if option=='environment' else ''}), \
                 patch.object(sys,'argv',['build.py',*(['--compiler','missing-fortran']
                                                       if option=='argument' else [])]), \
                 patch('shutil.which',return_value=None), \
                 patch('subprocess.run',side_effect=AssertionError(
                     'Missing compiler selection reached compiler invocation')) as run, \
                 patch.object(Path,'mkdir') as mkdir:
                with self.assertRaises(SystemExit) as raised:
                    runpy.run_path(str(ROOT/'build.py'),run_name='__main__')
                self.assertIn('missing-fortran',str(raised.exception))
                self.assertIn('PATH',str(raised.exception))
                run.assert_not_called()
                mkdir.assert_not_called()


if __name__=='__main__':
    unittest.main(verbosity=2)
