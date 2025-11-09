// dart
import 'package:flutter/material.dart';

class HomeScreen extends StatelessWidget {
  final String title;
  final String? userEmail;
  final VoidCallback? onSignOut;

  const HomeScreen({
    Key? key,
    this.title = 'Home',
    this.userEmail,
    this.onSignOut,
  }) : super(key: key);

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: Text(title),
        actions: [
          IconButton(
            icon: const Icon(Icons.logout),
            tooltip: 'Sign out',
            onPressed: onSignOut ??
                () {
                  // Default sign-out behavior: pop to first route
                  Navigator.of(context).popUntil((route) => route.isFirst);
                },
          ),
        ],
      ),
      body: Center(
        child: Padding(
          padding: const EdgeInsets.symmetric(horizontal: 24.0),
          child: Column(
            mainAxisSize: MainAxisSize.min,
            children: [
              Text(
                userEmail != null ? 'Welcome, $userEmail' : 'Welcome',
                style: Theme.of(context).textTheme.titleLarge,
                textAlign: TextAlign.center,
              ),
              const SizedBox(height: 12),
              const Text(
                'This is a basic home page. Replace with your content.',
                textAlign: TextAlign.center,
              ),
              const SizedBox(height: 20),
              ElevatedButton(
                onPressed: () {
                  // Example action: open a placeholder page
                  Navigator.of(context).push(
                    MaterialPageRoute(
                      builder: (_) => const _PlaceholderPage(),
                    ),
                  );
                },
                child: const Text('Explore'),
              ),
            ],
          ),
        ),
      ),
    );
  }
}

class _PlaceholderPage extends StatelessWidget {
  const _PlaceholderPage({Key? key}) : super(key: key);

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(title: const Text('Placeholder')),
      body: const Center(child: Text('Replace with real content')),
    );
  }
}