import 'package:app_ui/screens/home.dart';
import 'package:flutter/material.dart';
import 'package:local_auth/local_auth.dart';

class LoginScreen extends StatefulWidget {
  const LoginScreen({Key? key}) : super(key: key);

  @override
  _LoginScreenState createState() => _LoginScreenState();
}

class _LoginScreenState extends State<LoginScreen> {
  final _formKey = GlobalKey<FormState>();
  final TextEditingController _emailCtrl = TextEditingController();
  final TextEditingController _passwordCtrl = TextEditingController();

  final LocalAuthentication _localAuth = LocalAuthentication();

  bool _loading = false;
  bool _obscure = true;
  bool _hasBiometrics = false;
  bool _isAuthenticating = false;

  @override
  void initState() {
    super.initState();
    _emailCtrl.addListener(() => setState(() {}));
    _passwordCtrl.addListener(() => setState(() {}));
    _checkBiometrics();
  }

  Future<void> _checkBiometrics() async {
    try {
      final bool canCheck = await _localAuth.canCheckBiometrics;
      final bool isDeviceSupported = await _localAuth.isDeviceSupported();
      setState(() => _hasBiometrics = canCheck || isDeviceSupported);
    } catch (_) {
      setState(() => _hasBiometrics = false);
    }
  }

  Future<void> _authenticateWithBiometrics() async {
    try {
      setState(() => _isAuthenticating = true);
      final bool didAuthenticate = await _localAuth.authenticate(
        localizedReason: 'Authenticate to sign in',
        biometricOnly: true
      );
      setState(() => _isAuthenticating = false);

      if (!mounted) return;
      if (didAuthenticate) {
        // On success navigate. Use provided email if present, otherwise empty.
        Navigator.of(context).pushReplacement(
          MaterialPageRoute(
            builder: (_) => HomeScreen(userEmail: _emailCtrl.text.trim()),
          ),
        );
      } else {
        ScaffoldMessenger.of(context).showSnackBar(
          const SnackBar(content: Text('Biometric authentication failed')),
        );
      }
    } catch (e) {
      setState(() => _isAuthenticating = false);
      ScaffoldMessenger.of(context).showSnackBar(
        SnackBar(content: Text('Biometric error: $e')),
      );
    }
  }

  @override
  void dispose() {
    _emailCtrl.dispose();
    _passwordCtrl.dispose();
    super.dispose();
  }

  String? _emailValidator(String? v) {
    if (v == null || v.trim().isEmpty) return 'Enter your email';
    final emailRegex = RegExp(r'^[^@\s]+@[^@\s]+\.[^@\s]{2,}$');
    if (!emailRegex.hasMatch(v.trim())) return 'Enter a valid email';
    return null;
  }

  String? _passwordValidator(String? v) {
    if (v == null || v.isEmpty) return 'Enter your password';
    if (v.length < 6) return 'Password must be at least 6 characters';
    return null;
  }

  bool _isEmailValid() => _emailValidator(_emailCtrl.text) == null;
  bool _isPasswordValid() => _passwordValidator(_passwordCtrl.text) == null;
  bool _isFormValid() => _isEmailValid() && _isPasswordValid();

  Future<void> _submit() async {
    if (!_formKey.currentState!.validate()) return;
    setState(() => _loading = true);

    await Future.delayed(const Duration(seconds: 2));

    setState(() => _loading = false);

    ScaffoldMessenger.of(context).showSnackBar(
      const SnackBar(content: Text('Signed in successfully')),
    );

    Navigator.of(context).pushReplacement(
      MaterialPageRoute(builder: (_) => HomeScreen(userEmail: _emailCtrl.text.trim())),
    );
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(title: const Text('Login')),
      body: GestureDetector(
        onTap: () => FocusScope.of(context).unfocus(),
        child: SingleChildScrollView(
          padding: const EdgeInsets.symmetric(horizontal: 20, vertical: 32),
          child: Form(
            key: _formKey,
            autovalidateMode: AutovalidateMode.always,
            child: Column(
              children: [
                const SizedBox(height: 24),
                TextFormField(
                  controller: _emailCtrl,
                  keyboardType: TextInputType.emailAddress,
                  decoration: InputDecoration(
                    labelText: 'Email',
                    prefixIcon: const Icon(Icons.email),
                    border: const OutlineInputBorder(),
                    suffixIcon: _emailCtrl.text.isEmpty
                        ? null
                        : Icon(
                      _isEmailValid() ? Icons.check_circle : Icons.error,
                      color: _isEmailValid() ? Colors.green : Colors.red,
                    ),
                  ),
                  validator: _emailValidator,
                ),
                const SizedBox(height: 16),
                TextFormField(
                  controller: _passwordCtrl,
                  obscureText: _obscure,
                  decoration: InputDecoration(
                    labelText: 'Password',
                    prefixIcon: const Icon(Icons.lock),
                    border: const OutlineInputBorder(),
                    suffixIcon: Row(
                      mainAxisSize: MainAxisSize.min,
                      children: [
                        if (_passwordCtrl.text.isNotEmpty)
                          Icon(
                            _isPasswordValid() ? Icons.check_circle : Icons.error,
                            color: _isPasswordValid() ? Colors.green : Colors.red,
                          ),
                        IconButton(
                          icon: Icon(_obscure ? Icons.visibility : Icons.visibility_off),
                          onPressed: () => setState(() => _obscure = !_obscure),
                        ),
                      ],
                    ),
                  ),
                  validator: _passwordValidator,
                ),
                const SizedBox(height: 24),
                if (_hasBiometrics)
                  SizedBox(
                    width: double.infinity,
                    height: 48,
                    child: ElevatedButton.icon(
                      onPressed: _isAuthenticating || _loading ? null : _authenticateWithBiometrics,
                      icon: const Icon(Icons.fingerprint),
                      label: _isAuthenticating
                          ? const SizedBox(
                        width: 20,
                        height: 20,
                        child: CircularProgressIndicator(strokeWidth: 2, color: Colors.white),
                      )
                          : const Text('Sign in with fingerprint'),
                    ),
                  ),
                if (_hasBiometrics) const SizedBox(height: 12),
                SizedBox(
                  width: double.infinity,
                  height: 48,
                  child: ElevatedButton(
                    onPressed: (_loading || !_isFormValid()) ? null : _submit,
                    child: _loading
                        ? const SizedBox(
                      width: 20,
                      height: 20,
                      child: CircularProgressIndicator(strokeWidth: 2, color: Colors.white),
                    )
                        : const Text('Sign In'),
                  ),
                ),
              ],
            ),
          ),
        ),
      ),
    );
  }
}
